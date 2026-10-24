import FiniteExclusionKernel

set_option maxRecDepth 4096
set_option maxHeartbeats 20000000

namespace Delivery.FiniteExclusion.Cycle9
open FiniteGame Extremal

def a (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 0
  | _ => 0

theorem node_2 : Excluded a [2] :=
  source_excluded a [2] 0 3 1 (by decide) (by decide +kernel)

theorem node_4 : Excluded a [3,0] :=
  predecessor_excluded a [3,0] 4 3 1 0 (by decide) (by decide +kernel)

theorem node_5 : Excluded a [3,4] :=
  predecessor_excluded a [3,4] 2 4 0 1 (by decide) (by decide +kernel)

theorem node_7 : Excluded a [3,5,0] :=
  source_excluded a [3,5,0] 2 1 0 (by decide) (by decide +kernel)

theorem node_8 : Excluded a [3,5,1] :=
  source_excluded a [3,5,1] 0 2 2 (by decide) (by decide +kernel)

theorem node_9 : Excluded a [3,5,4] :=
  source_excluded a [3,5,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_10 : Excluded a [3,5,6] :=
  predecessor_excluded a [3,5,6] 0 6 1 2 (by decide) (by decide +kernel)

theorem node_13 : Excluded a [3,5,7,0,1] :=
  source_excluded a [3,5,7,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_14 : Excluded a [3,5,7,0,2] :=
  source_excluded a [3,5,7,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_15 : Excluded a [3,5,7,0,6] :=
  source_excluded a [3,5,7,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_18 : Excluded a [3,5,7,0,8,1,2] :=
  source_excluded a [3,5,7,0,8,1,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_19 : Excluded a [3,5,7,0,8,1,4] :=
  predecessor_excluded a [3,5,7,0,8,1,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_17 : Excluded a [3,5,7,0,8,1] :=
  branch_excluded a [3,5,7,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,1,1] (by decide +kernel))
      node_18
      (invalid_excluded a [3,5,7,0,8,1,3] (by decide +kernel))
      node_19
      (invalid_excluded a [3,5,7,0,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,1,8] (by decide +kernel)))

theorem node_20 : Excluded a [3,5,7,0,8,2] :=
  source_excluded a [3,5,7,0,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_23 : Excluded a [3,5,7,0,8,4,1,2] :=
  predecessor_excluded a [3,5,7,0,8,4,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_25 : Excluded a [3,5,7,0,8,4,1,6,2] :=
  predecessor_excluded a [3,5,7,0,8,4,1,6,2] 1 3 8 0 (by decide) (by decide +kernel)

theorem node_24 : Excluded a [3,5,7,0,8,4,1,6] :=
  branch_excluded a [3,5,7,0,8,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,8,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,6,1] (by decide +kernel))
      node_25
      (invalid_excluded a [3,5,7,0,8,4,1,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,6,8] (by decide +kernel)))

theorem node_22 : Excluded a [3,5,7,0,8,4,1] :=
  branch_excluded a [3,5,7,0,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,1] (by decide +kernel))
      node_23
      (invalid_excluded a [3,5,7,0,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,5] (by decide +kernel))
      node_24
      (invalid_excluded a [3,5,7,0,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,1,8] (by decide +kernel)))

theorem node_26 : Excluded a [3,5,7,0,8,4,2] :=
  source_excluded a [3,5,7,0,8,4,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_21 : Excluded a [3,5,7,0,8,4] :=
  branch_excluded a [3,5,7,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,8,4,0] (by decide +kernel))
      node_22
      node_26
      (invalid_excluded a [3,5,7,0,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,4,8] (by decide +kernel)))

theorem node_16 : Excluded a [3,5,7,0,8] :=
  branch_excluded a [3,5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,8,0] (by decide +kernel))
      node_17
      node_20
      (invalid_excluded a [3,5,7,0,8,3] (by decide +kernel))
      node_21
      (invalid_excluded a [3,5,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,8,8] (by decide +kernel)))

theorem node_12 : Excluded a [3,5,7,0] :=
  branch_excluded a [3,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,0,0] (by decide +kernel))
      node_13
      node_14
      (invalid_excluded a [3,5,7,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,0,5] (by decide +kernel))
      node_15
      (invalid_excluded a [3,5,7,0,7] (by decide +kernel))
      node_16)

theorem node_27 : Excluded a [3,5,7,1] :=
  source_excluded a [3,5,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_28 : Excluded a [3,5,7,2] :=
  predecessor_excluded a [3,5,7,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_31 : Excluded a [3,5,7,6,0,1] :=
  predecessor_excluded a [3,5,7,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_32 : Excluded a [3,5,7,6,0,2] :=
  source_excluded a [3,5,7,6,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_33 : Excluded a [3,5,7,6,0,4] :=
  source_excluded a [3,5,7,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_36 : Excluded a [3,5,7,6,0,8,1,2] :=
  predecessor_excluded a [3,5,7,6,0,8,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_37 : Excluded a [3,5,7,6,0,8,1,4] :=
  predecessor_excluded a [3,5,7,6,0,8,1,4] 1 0 7 4 (by decide) (by decide +kernel)

theorem node_35 : Excluded a [3,5,7,6,0,8,1] :=
  branch_excluded a [3,5,7,6,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,6,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,1,1] (by decide +kernel))
      node_36
      (invalid_excluded a [3,5,7,6,0,8,1,3] (by decide +kernel))
      node_37
      (invalid_excluded a [3,5,7,6,0,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,1,8] (by decide +kernel)))

theorem node_38 : Excluded a [3,5,7,6,0,8,2] :=
  source_excluded a [3,5,7,6,0,8,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_39 : Excluded a [3,5,7,6,0,8,4] :=
  source_excluded a [3,5,7,6,0,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_34 : Excluded a [3,5,7,6,0,8] :=
  branch_excluded a [3,5,7,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,6,0,8,0] (by decide +kernel))
      node_35
      node_38
      (invalid_excluded a [3,5,7,6,0,8,3] (by decide +kernel))
      node_39
      (invalid_excluded a [3,5,7,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,8,8] (by decide +kernel)))

theorem node_30 : Excluded a [3,5,7,6,0] :=
  branch_excluded a [3,5,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,6,0,0] (by decide +kernel))
      node_31
      node_32
      (invalid_excluded a [3,5,7,6,0,3] (by decide +kernel))
      node_33
      (invalid_excluded a [3,5,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,0,7] (by decide +kernel))
      node_34)

theorem node_40 : Excluded a [3,5,7,6,1] :=
  source_excluded a [3,5,7,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_41 : Excluded a [3,5,7,6,2] :=
  source_excluded a [3,5,7,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_43 : Excluded a [3,5,7,6,8,0] :=
  predecessor_excluded a [3,5,7,6,8,0] 1 0 4 5 (by decide) (by decide +kernel)

def b_47 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 7
  | 3 => 6
  | 4 => 8
  | 5 => 1
  | 6 => 0
  | 7 => 2
  | 8 => 4
  | _ => 0

def cert_47 : LosingRegion (edgeOf a b_47) 1 :=
  losingMask a b_47 1 1212620934163931226701825
    (by decide +kernel) (by decide +kernel)

theorem node_47 : Excluded a [3,5,7,6,8,1,0,2,4] :=
  losing_excluded a [3,5,7,6,8,1,0,2,4] (by decide) b_47 (by decide +kernel) 2 1 3 cert_47 (by change 2 ≠ 1 ∧ ¬ edgeOf a b_47 2 1 ∧ 3 ≠ 2 ∧ maskRegion 1212620934163931226701825 2 3; decide +kernel)

theorem node_46 : Excluded a [3,5,7,6,8,1,0,2] :=
  branch_excluded a [3,5,7,6,8,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,6,8,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,0,2,3] (by decide +kernel))
      node_47
      (invalid_excluded a [3,5,7,6,8,1,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,0,2,8] (by decide +kernel)))

theorem node_48 : Excluded a [3,5,7,6,8,1,0,4] :=
  source_excluded a [3,5,7,6,8,1,0,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_45 : Excluded a [3,5,7,6,8,1,0] :=
  branch_excluded a [3,5,7,6,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,6,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,0,1] (by decide +kernel))
      node_46
      (invalid_excluded a [3,5,7,6,8,1,0,3] (by decide +kernel))
      node_48
      (invalid_excluded a [3,5,7,6,8,1,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,0,8] (by decide +kernel)))

theorem node_49 : Excluded a [3,5,7,6,8,1,2] :=
  source_excluded a [3,5,7,6,8,1,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_50 : Excluded a [3,5,7,6,8,1,4] :=
  source_excluded a [3,5,7,6,8,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_44 : Excluded a [3,5,7,6,8,1] :=
  branch_excluded a [3,5,7,6,8,1] (by decide)
    (fin9_cases _
      node_45
      (invalid_excluded a [3,5,7,6,8,1,1] (by decide +kernel))
      node_49
      (invalid_excluded a [3,5,7,6,8,1,3] (by decide +kernel))
      node_50
      (invalid_excluded a [3,5,7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,1,8] (by decide +kernel)))

theorem node_51 : Excluded a [3,5,7,6,8,2] :=
  source_excluded a [3,5,7,6,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_52 : Excluded a [3,5,7,6,8,4] :=
  source_excluded a [3,5,7,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_42 : Excluded a [3,5,7,6,8] :=
  branch_excluded a [3,5,7,6,8] (by decide)
    (fin9_cases _
      node_43
      node_44
      node_51
      (invalid_excluded a [3,5,7,6,8,3] (by decide +kernel))
      node_52
      (invalid_excluded a [3,5,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,8] (by decide +kernel)))

theorem node_29 : Excluded a [3,5,7,6] :=
  branch_excluded a [3,5,7,6] (by decide)
    (fin9_cases _
      node_30
      node_40
      node_41
      (invalid_excluded a [3,5,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,7] (by decide +kernel))
      node_42)

theorem node_53 : Excluded a [3,5,7,8] :=
  predecessor_excluded a [3,5,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_11 : Excluded a [3,5,7] :=
  branch_excluded a [3,5,7] (by decide)
    (fin9_cases _
      node_12
      node_27
      node_28
      (invalid_excluded a [3,5,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,5] (by decide +kernel))
      node_29
      (invalid_excluded a [3,5,7,7] (by decide +kernel))
      node_53)

theorem node_55 : Excluded a [3,5,8,0] :=
  predecessor_excluded a [3,5,8,0] 1 0 2 3 (by decide) (by decide +kernel)

theorem node_56 : Excluded a [3,5,8,1] :=
  source_excluded a [3,5,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_57 : Excluded a [3,5,8,2] :=
  predecessor_excluded a [3,5,8,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_60 : Excluded a [3,5,8,6,0,1] :=
  predecessor_excluded a [3,5,8,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_61 : Excluded a [3,5,8,6,0,2] :=
  source_excluded a [3,5,8,6,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_62 : Excluded a [3,5,8,6,0,4] :=
  source_excluded a [3,5,8,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_63 : Excluded a [3,5,8,6,0,7] :=
  source_excluded a [3,5,8,6,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_59 : Excluded a [3,5,8,6,0] :=
  branch_excluded a [3,5,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,6,0,0] (by decide +kernel))
      node_60
      node_61
      (invalid_excluded a [3,5,8,6,0,3] (by decide +kernel))
      node_62
      (invalid_excluded a [3,5,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,0,6] (by decide +kernel))
      node_63
      (invalid_excluded a [3,5,8,6,0,8] (by decide +kernel)))

theorem node_64 : Excluded a [3,5,8,6,1] :=
  source_excluded a [3,5,8,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_65 : Excluded a [3,5,8,6,2] :=
  source_excluded a [3,5,8,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_66 : Excluded a [3,5,8,6,7] :=
  predecessor_excluded a [3,5,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_58 : Excluded a [3,5,8,6] :=
  branch_excluded a [3,5,8,6] (by decide)
    (fin9_cases _
      node_59
      node_64
      node_65
      (invalid_excluded a [3,5,8,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,6] (by decide +kernel))
      node_66
      (invalid_excluded a [3,5,8,6,8] (by decide +kernel)))

theorem node_69 : Excluded a [3,5,8,7,0,1] :=
  predecessor_excluded a [3,5,8,7,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_70 : Excluded a [3,5,8,7,0,2] :=
  source_excluded a [3,5,8,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_73 : Excluded a [3,5,8,7,0,4,1,2] :=
  source_excluded a [3,5,8,7,0,4,1,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_75 : Excluded a [3,5,8,7,0,4,1,6,2] :=
  predecessor_excluded a [3,5,8,7,0,4,1,6,2] 1 3 8 0 (by decide) (by decide +kernel)

theorem node_74 : Excluded a [3,5,8,7,0,4,1,6] :=
  branch_excluded a [3,5,8,7,0,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,7,0,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,1,6,1] (by decide +kernel))
      node_75
      (invalid_excluded a [3,5,8,7,0,4,1,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,1,6,8] (by decide +kernel)))

theorem node_72 : Excluded a [3,5,8,7,0,4,1] :=
  branch_excluded a [3,5,8,7,0,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,7,0,4,1,0] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,1,1] (by decide +kernel))
      node_73
      (invalid_excluded a [3,5,8,7,0,4,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,1,5] (by decide +kernel))
      node_74
      (invalid_excluded a [3,5,8,7,0,4,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,1,8] (by decide +kernel)))

theorem node_76 : Excluded a [3,5,8,7,0,4,2] :=
  predecessor_excluded a [3,5,8,7,0,4,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_71 : Excluded a [3,5,8,7,0,4] :=
  branch_excluded a [3,5,8,7,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,7,0,4,0] (by decide +kernel))
      node_72
      node_76
      (invalid_excluded a [3,5,8,7,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,4,8] (by decide +kernel)))

theorem node_68 : Excluded a [3,5,8,7,0] :=
  branch_excluded a [3,5,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,7,0,0] (by decide +kernel))
      node_69
      node_70
      (invalid_excluded a [3,5,8,7,0,3] (by decide +kernel))
      node_71
      (invalid_excluded a [3,5,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,0,8] (by decide +kernel)))

theorem node_77 : Excluded a [3,5,8,7,1] :=
  source_excluded a [3,5,8,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_78 : Excluded a [3,5,8,7,2] :=
  source_excluded a [3,5,8,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_79 : Excluded a [3,5,8,7,6] :=
  source_excluded a [3,5,8,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_67 : Excluded a [3,5,8,7] :=
  branch_excluded a [3,5,8,7] (by decide)
    (fin9_cases _
      node_68
      node_77
      node_78
      (invalid_excluded a [3,5,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,5] (by decide +kernel))
      node_79
      (invalid_excluded a [3,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,8] (by decide +kernel)))

theorem node_54 : Excluded a [3,5,8] :=
  branch_excluded a [3,5,8] (by decide)
    (fin9_cases _
      node_55
      node_56
      node_57
      (invalid_excluded a [3,5,8,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,5] (by decide +kernel))
      node_58
      node_67
      (invalid_excluded a [3,5,8,8] (by decide +kernel)))

theorem node_6 : Excluded a [3,5] :=
  branch_excluded a [3,5] (by decide)
    (fin9_cases _
      node_7
      node_8
      (invalid_excluded a [3,5,2] (by decide +kernel))
      (invalid_excluded a [3,5,3] (by decide +kernel))
      node_9
      (invalid_excluded a [3,5,5] (by decide +kernel))
      node_10
      node_11
      node_54)

theorem node_81 : Excluded a [3,6,0] :=
  source_excluded a [3,6,0] 2 1 0 (by decide) (by decide +kernel)

theorem node_82 : Excluded a [3,6,1] :=
  source_excluded a [3,6,1] 0 2 2 (by decide) (by decide +kernel)

theorem node_83 : Excluded a [3,6,4] :=
  source_excluded a [3,6,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_86 : Excluded a [3,6,5,0,1] :=
  predecessor_excluded a [3,6,5,0,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_87 : Excluded a [3,6,5,0,2] :=
  source_excluded a [3,6,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_89 : Excluded a [3,6,5,0,7,1] :=
  source_excluded a [3,6,5,0,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_90 : Excluded a [3,6,5,0,7,2] :=
  source_excluded a [3,6,5,0,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_91 : Excluded a [3,6,5,0,7,4] :=
  predecessor_excluded a [3,6,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_92 : Excluded a [3,6,5,0,7,8] :=
  predecessor_excluded a [3,6,5,0,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_88 : Excluded a [3,6,5,0,7] :=
  branch_excluded a [3,6,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,0,7,0] (by decide +kernel))
      node_89
      node_90
      (invalid_excluded a [3,6,5,0,7,3] (by decide +kernel))
      node_91
      (invalid_excluded a [3,6,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,7,7] (by decide +kernel))
      node_92)

theorem node_94 : Excluded a [3,6,5,0,8,1] :=
  source_excluded a [3,6,5,0,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_95 : Excluded a [3,6,5,0,8,2] :=
  source_excluded a [3,6,5,0,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_96 : Excluded a [3,6,5,0,8,4] :=
  predecessor_excluded a [3,6,5,0,8,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_97 : Excluded a [3,6,5,0,8,7] :=
  source_excluded a [3,6,5,0,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_93 : Excluded a [3,6,5,0,8] :=
  branch_excluded a [3,6,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,0,8,0] (by decide +kernel))
      node_94
      node_95
      (invalid_excluded a [3,6,5,0,8,3] (by decide +kernel))
      node_96
      (invalid_excluded a [3,6,5,0,8,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,8,6] (by decide +kernel))
      node_97
      (invalid_excluded a [3,6,5,0,8,8] (by decide +kernel)))

theorem node_85 : Excluded a [3,6,5,0] :=
  branch_excluded a [3,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,0,0] (by decide +kernel))
      node_86
      node_87
      (invalid_excluded a [3,6,5,0,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,0,6] (by decide +kernel))
      node_88
      node_93)

theorem node_98 : Excluded a [3,6,5,1] :=
  source_excluded a [3,6,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_99 : Excluded a [3,6,5,2] :=
  predecessor_excluded a [3,6,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_102 : Excluded a [3,6,5,7,0,1] :=
  source_excluded a [3,6,5,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_103 : Excluded a [3,6,5,7,0,2] :=
  source_excluded a [3,6,5,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_104 : Excluded a [3,6,5,7,0,4] :=
  predecessor_excluded a [3,6,5,7,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_107 : Excluded a [3,6,5,7,0,8,1,2] :=
  predecessor_excluded a [3,6,5,7,0,8,1,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_108 : Excluded a [3,6,5,7,0,8,1,4] :=
  source_excluded a [3,6,5,7,0,8,1,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_106 : Excluded a [3,6,5,7,0,8,1] :=
  branch_excluded a [3,6,5,7,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,7,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,8,1,1] (by decide +kernel))
      node_107
      (invalid_excluded a [3,6,5,7,0,8,1,3] (by decide +kernel))
      node_108
      (invalid_excluded a [3,6,5,7,0,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,8,1,8] (by decide +kernel)))

theorem node_109 : Excluded a [3,6,5,7,0,8,2] :=
  source_excluded a [3,6,5,7,0,8,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_110 : Excluded a [3,6,5,7,0,8,4] :=
  source_excluded a [3,6,5,7,0,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_105 : Excluded a [3,6,5,7,0,8] :=
  branch_excluded a [3,6,5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,7,0,8,0] (by decide +kernel))
      node_106
      node_109
      (invalid_excluded a [3,6,5,7,0,8,3] (by decide +kernel))
      node_110
      (invalid_excluded a [3,6,5,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,8,8] (by decide +kernel)))

theorem node_101 : Excluded a [3,6,5,7,0] :=
  branch_excluded a [3,6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,7,0,0] (by decide +kernel))
      node_102
      node_103
      (invalid_excluded a [3,6,5,7,0,3] (by decide +kernel))
      node_104
      (invalid_excluded a [3,6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,7] (by decide +kernel))
      node_105)

theorem node_111 : Excluded a [3,6,5,7,1] :=
  predecessor_excluded a [3,6,5,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_112 : Excluded a [3,6,5,7,2] :=
  source_excluded a [3,6,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_113 : Excluded a [3,6,5,7,8] :=
  predecessor_excluded a [3,6,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_100 : Excluded a [3,6,5,7] :=
  branch_excluded a [3,6,5,7] (by decide)
    (fin9_cases _
      node_101
      node_111
      node_112
      (invalid_excluded a [3,6,5,7,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,7] (by decide +kernel))
      node_113)

theorem node_115 : Excluded a [3,6,5,8,0] :=
  predecessor_excluded a [3,6,5,8,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_116 : Excluded a [3,6,5,8,1] :=
  predecessor_excluded a [3,6,5,8,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_117 : Excluded a [3,6,5,8,2] :=
  source_excluded a [3,6,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_120 : Excluded a [3,6,5,8,7,0,1] :=
  predecessor_excluded a [3,6,5,8,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_121 : Excluded a [3,6,5,8,7,0,2] :=
  source_excluded a [3,6,5,8,7,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_122 : Excluded a [3,6,5,8,7,0,4] :=
  source_excluded a [3,6,5,8,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_119 : Excluded a [3,6,5,8,7,0] :=
  branch_excluded a [3,6,5,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,8,7,0,0] (by decide +kernel))
      node_120
      node_121
      (invalid_excluded a [3,6,5,8,7,0,3] (by decide +kernel))
      node_122
      (invalid_excluded a [3,6,5,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,0,8] (by decide +kernel)))

theorem node_123 : Excluded a [3,6,5,8,7,1] :=
  source_excluded a [3,6,5,8,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_124 : Excluded a [3,6,5,8,7,2] :=
  source_excluded a [3,6,5,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_125 : Excluded a [3,6,5,8,7,4] :=
  predecessor_excluded a [3,6,5,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_118 : Excluded a [3,6,5,8,7] :=
  branch_excluded a [3,6,5,8,7] (by decide)
    (fin9_cases _
      node_119
      node_123
      node_124
      (invalid_excluded a [3,6,5,8,7,3] (by decide +kernel))
      node_125
      (invalid_excluded a [3,6,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,8] (by decide +kernel)))

theorem node_114 : Excluded a [3,6,5,8] :=
  branch_excluded a [3,6,5,8] (by decide)
    (fin9_cases _
      node_115
      node_116
      node_117
      (invalid_excluded a [3,6,5,8,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,6] (by decide +kernel))
      node_118
      (invalid_excluded a [3,6,5,8,8] (by decide +kernel)))

theorem node_84 : Excluded a [3,6,5] :=
  branch_excluded a [3,6,5] (by decide)
    (fin9_cases _
      node_85
      node_98
      node_99
      (invalid_excluded a [3,6,5,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,6] (by decide +kernel))
      node_100
      node_114)

theorem node_126 : Excluded a [3,6,7] :=
  predecessor_excluded a [3,6,7] 0 7 1 2 (by decide) (by decide +kernel)

theorem node_128 : Excluded a [3,6,8,0] :=
  predecessor_excluded a [3,6,8,0] 1 0 2 3 (by decide) (by decide +kernel)

theorem node_129 : Excluded a [3,6,8,1] :=
  source_excluded a [3,6,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_130 : Excluded a [3,6,8,2] :=
  predecessor_excluded a [3,6,8,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_131 : Excluded a [3,6,8,5] :=
  source_excluded a [3,6,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_134 : Excluded a [3,6,8,7,0,1] :=
  source_excluded a [3,6,8,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_135 : Excluded a [3,6,8,7,0,2] :=
  source_excluded a [3,6,8,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_138 : Excluded a [3,6,8,7,0,4,1,2] :=
  source_excluded a [3,6,8,7,0,4,1,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_139 : Excluded a [3,6,8,7,0,4,1,5] :=
  predecessor_excluded a [3,6,8,7,0,4,1,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_137 : Excluded a [3,6,8,7,0,4,1] :=
  branch_excluded a [3,6,8,7,0,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,7,0,4,1,0] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,4,1,1] (by decide +kernel))
      node_138
      (invalid_excluded a [3,6,8,7,0,4,1,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,4,1,4] (by decide +kernel))
      node_139
      (invalid_excluded a [3,6,8,7,0,4,1,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,4,1,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,4,1,8] (by decide +kernel)))

theorem node_140 : Excluded a [3,6,8,7,0,4,2] :=
  source_excluded a [3,6,8,7,0,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_141 : Excluded a [3,6,8,7,0,4,5] :=
  predecessor_excluded a [3,6,8,7,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_136 : Excluded a [3,6,8,7,0,4] :=
  branch_excluded a [3,6,8,7,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,7,0,4,0] (by decide +kernel))
      node_137
      node_140
      (invalid_excluded a [3,6,8,7,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,4,4] (by decide +kernel))
      node_141
      (invalid_excluded a [3,6,8,7,0,4,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,4,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,4,8] (by decide +kernel)))

theorem node_133 : Excluded a [3,6,8,7,0] :=
  branch_excluded a [3,6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,7,0,0] (by decide +kernel))
      node_134
      node_135
      (invalid_excluded a [3,6,8,7,0,3] (by decide +kernel))
      node_136
      (invalid_excluded a [3,6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,8] (by decide +kernel)))

theorem node_142 : Excluded a [3,6,8,7,1] :=
  predecessor_excluded a [3,6,8,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_145 : Excluded a [3,6,8,7,2,0,1] :=
  predecessor_excluded a [3,6,8,7,2,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_146 : Excluded a [3,6,8,7,2,0,4] :=
  source_excluded a [3,6,8,7,2,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_149 : Excluded a [3,6,8,7,2,0,5,1,4] :=
  predecessor_excluded a [3,6,8,7,2,0,5,1,4] 0 4 2 8 (by decide) (by decide +kernel)

theorem node_148 : Excluded a [3,6,8,7,2,0,5,1] :=
  branch_excluded a [3,6,8,7,2,0,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,7,2,0,5,1,0] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,0,5,1,1] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,0,5,1,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,0,5,1,3] (by decide +kernel))
      node_149
      (invalid_excluded a [3,6,8,7,2,0,5,1,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,0,5,1,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,0,5,1,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,0,5,1,8] (by decide +kernel)))

theorem node_150 : Excluded a [3,6,8,7,2,0,5,4] :=
  source_excluded a [3,6,8,7,2,0,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_147 : Excluded a [3,6,8,7,2,0,5] :=
  branch_excluded a [3,6,8,7,2,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,7,2,0,5,0] (by decide +kernel))
      node_148
      (invalid_excluded a [3,6,8,7,2,0,5,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,0,5,3] (by decide +kernel))
      node_150
      (invalid_excluded a [3,6,8,7,2,0,5,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,0,5,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,0,5,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,0,5,8] (by decide +kernel)))

theorem node_144 : Excluded a [3,6,8,7,2,0] :=
  branch_excluded a [3,6,8,7,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,7,2,0,0] (by decide +kernel))
      node_145
      (invalid_excluded a [3,6,8,7,2,0,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,0,3] (by decide +kernel))
      node_146
      node_147
      (invalid_excluded a [3,6,8,7,2,0,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,0,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,0,8] (by decide +kernel)))

theorem node_151 : Excluded a [3,6,8,7,2,1] :=
  source_excluded a [3,6,8,7,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_154 : Excluded a [3,6,8,7,2,4,0,1] :=
  predecessor_excluded a [3,6,8,7,2,4,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_155 : Excluded a [3,6,8,7,2,4,0,5] :=
  predecessor_excluded a [3,6,8,7,2,4,0,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_153 : Excluded a [3,6,8,7,2,4,0] :=
  branch_excluded a [3,6,8,7,2,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,7,2,4,0,0] (by decide +kernel))
      node_154
      (invalid_excluded a [3,6,8,7,2,4,0,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,0,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,0,4] (by decide +kernel))
      node_155
      (invalid_excluded a [3,6,8,7,2,4,0,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,0,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,0,8] (by decide +kernel)))

theorem node_157 : Excluded a [3,6,8,7,2,4,1,0] :=
  source_excluded a [3,6,8,7,2,4,1,0] 7 1 8 (by decide) (by decide +kernel)

theorem node_158 : Excluded a [3,6,8,7,2,4,1,5] :=
  predecessor_excluded a [3,6,8,7,2,4,1,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_156 : Excluded a [3,6,8,7,2,4,1] :=
  branch_excluded a [3,6,8,7,2,4,1] (by decide)
    (fin9_cases _
      node_157
      (invalid_excluded a [3,6,8,7,2,4,1,1] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,1,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,1,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,1,4] (by decide +kernel))
      node_158
      (invalid_excluded a [3,6,8,7,2,4,1,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,1,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,1,8] (by decide +kernel)))

theorem node_159 : Excluded a [3,6,8,7,2,4,5] :=
  predecessor_excluded a [3,6,8,7,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_152 : Excluded a [3,6,8,7,2,4] :=
  branch_excluded a [3,6,8,7,2,4] (by decide)
    (fin9_cases _
      node_153
      node_156
      (invalid_excluded a [3,6,8,7,2,4,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,4] (by decide +kernel))
      node_159
      (invalid_excluded a [3,6,8,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,8] (by decide +kernel)))

theorem node_143 : Excluded a [3,6,8,7,2] :=
  branch_excluded a [3,6,8,7,2] (by decide)
    (fin9_cases _
      node_144
      node_151
      (invalid_excluded a [3,6,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,3] (by decide +kernel))
      node_152
      (invalid_excluded a [3,6,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,8] (by decide +kernel)))

theorem node_132 : Excluded a [3,6,8,7] :=
  branch_excluded a [3,6,8,7] (by decide)
    (fin9_cases _
      node_133
      node_142
      node_143
      (invalid_excluded a [3,6,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,8] (by decide +kernel)))

theorem node_127 : Excluded a [3,6,8] :=
  branch_excluded a [3,6,8] (by decide)
    (fin9_cases _
      node_128
      node_129
      node_130
      (invalid_excluded a [3,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,4] (by decide +kernel))
      node_131
      (invalid_excluded a [3,6,8,6] (by decide +kernel))
      node_132
      (invalid_excluded a [3,6,8,8] (by decide +kernel)))

theorem node_80 : Excluded a [3,6] :=
  branch_excluded a [3,6] (by decide)
    (fin9_cases _
      node_81
      node_82
      (invalid_excluded a [3,6,2] (by decide +kernel))
      (invalid_excluded a [3,6,3] (by decide +kernel))
      node_83
      node_84
      (invalid_excluded a [3,6,6] (by decide +kernel))
      node_126
      node_127)

theorem node_161 : Excluded a [3,7,0] :=
  source_excluded a [3,7,0] 2 1 0 (by decide) (by decide +kernel)

theorem node_162 : Excluded a [3,7,1] :=
  source_excluded a [3,7,1] 0 2 2 (by decide) (by decide +kernel)

theorem node_163 : Excluded a [3,7,4] :=
  source_excluded a [3,7,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_166 : Excluded a [3,7,5,0,1] :=
  predecessor_excluded a [3,7,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_167 : Excluded a [3,7,5,0,2] :=
  source_excluded a [3,7,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_168 : Excluded a [3,7,5,0,6] :=
  source_excluded a [3,7,5,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_170 : Excluded a [3,7,5,0,8,1] :=
  predecessor_excluded a [3,7,5,0,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_172 : Excluded a [3,7,5,0,8,2,1] :=
  source_excluded a [3,7,5,0,8,2,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_173 : Excluded a [3,7,5,0,8,2,4] :=
  predecessor_excluded a [3,7,5,0,8,2,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_171 : Excluded a [3,7,5,0,8,2] :=
  branch_excluded a [3,7,5,0,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,0,8,2,0] (by decide +kernel))
      node_172
      (invalid_excluded a [3,7,5,0,8,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,2,3] (by decide +kernel))
      node_173
      (invalid_excluded a [3,7,5,0,8,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,2,8] (by decide +kernel)))

theorem node_174 : Excluded a [3,7,5,0,8,4] :=
  predecessor_excluded a [3,7,5,0,8,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_169 : Excluded a [3,7,5,0,8] :=
  branch_excluded a [3,7,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,0,8,0] (by decide +kernel))
      node_170
      node_171
      (invalid_excluded a [3,7,5,0,8,3] (by decide +kernel))
      node_174
      (invalid_excluded a [3,7,5,0,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,8,8] (by decide +kernel)))

theorem node_165 : Excluded a [3,7,5,0] :=
  branch_excluded a [3,7,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,0,0] (by decide +kernel))
      node_166
      node_167
      (invalid_excluded a [3,7,5,0,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,0,5] (by decide +kernel))
      node_168
      (invalid_excluded a [3,7,5,0,7] (by decide +kernel))
      node_169)

theorem node_175 : Excluded a [3,7,5,1] :=
  source_excluded a [3,7,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_176 : Excluded a [3,7,5,2] :=
  predecessor_excluded a [3,7,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_177 : Excluded a [3,7,5,6] :=
  predecessor_excluded a [3,7,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_179 : Excluded a [3,7,5,8,0] :=
  predecessor_excluded a [3,7,5,8,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_182 : Excluded a [3,7,5,8,1,0,2] :=
  source_excluded a [3,7,5,8,1,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_184 : Excluded a [3,7,5,8,1,0,4,2] :=
  source_excluded a [3,7,5,8,1,0,4,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_186 : Excluded a [3,7,5,8,1,0,4,6,2] :=
  predecessor_excluded a [3,7,5,8,1,0,4,6,2] 1 3 8 0 (by decide) (by decide +kernel)

theorem node_185 : Excluded a [3,7,5,8,1,0,4,6] :=
  branch_excluded a [3,7,5,8,1,0,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,1,0,4,6,0] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,6,1] (by decide +kernel))
      node_186
      (invalid_excluded a [3,7,5,8,1,0,4,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,6,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,6,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,6,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,6,8] (by decide +kernel)))

theorem node_183 : Excluded a [3,7,5,8,1,0,4] :=
  branch_excluded a [3,7,5,8,1,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,1,0,4,0] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,1] (by decide +kernel))
      node_184
      (invalid_excluded a [3,7,5,8,1,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,5] (by decide +kernel))
      node_185
      (invalid_excluded a [3,7,5,8,1,0,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,8] (by decide +kernel)))

theorem node_181 : Excluded a [3,7,5,8,1,0] :=
  branch_excluded a [3,7,5,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,1] (by decide +kernel))
      node_182
      (invalid_excluded a [3,7,5,8,1,0,3] (by decide +kernel))
      node_183
      (invalid_excluded a [3,7,5,8,1,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,8] (by decide +kernel)))

theorem node_187 : Excluded a [3,7,5,8,1,2] :=
  predecessor_excluded a [3,7,5,8,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_188 : Excluded a [3,7,5,8,1,4] :=
  predecessor_excluded a [3,7,5,8,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_180 : Excluded a [3,7,5,8,1] :=
  branch_excluded a [3,7,5,8,1] (by decide)
    (fin9_cases _
      node_181
      (invalid_excluded a [3,7,5,8,1,1] (by decide +kernel))
      node_187
      (invalid_excluded a [3,7,5,8,1,3] (by decide +kernel))
      node_188
      (invalid_excluded a [3,7,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,8] (by decide +kernel)))

theorem node_189 : Excluded a [3,7,5,8,2] :=
  source_excluded a [3,7,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_190 : Excluded a [3,7,5,8,6] :=
  source_excluded a [3,7,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_178 : Excluded a [3,7,5,8] :=
  branch_excluded a [3,7,5,8] (by decide)
    (fin9_cases _
      node_179
      node_180
      node_189
      (invalid_excluded a [3,7,5,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,5] (by decide +kernel))
      node_190
      (invalid_excluded a [3,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,8] (by decide +kernel)))

theorem node_164 : Excluded a [3,7,5] :=
  branch_excluded a [3,7,5] (by decide)
    (fin9_cases _
      node_165
      node_175
      node_176
      (invalid_excluded a [3,7,5,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,5] (by decide +kernel))
      node_177
      (invalid_excluded a [3,7,5,7] (by decide +kernel))
      node_178)

theorem node_193 : Excluded a [3,7,6,0,1] :=
  predecessor_excluded a [3,7,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_194 : Excluded a [3,7,6,0,2] :=
  predecessor_excluded a [3,7,6,0,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_196 : Excluded a [3,7,6,0,8,1] :=
  predecessor_excluded a [3,7,6,0,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_197 : Excluded a [3,7,6,0,8,2] :=
  source_excluded a [3,7,6,0,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_199 : Excluded a [3,7,6,0,8,4,1] :=
  source_excluded a [3,7,6,0,8,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_200 : Excluded a [3,7,6,0,8,4,2] :=
  source_excluded a [3,7,6,0,8,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_201 : Excluded a [3,7,6,0,8,4,5] :=
  predecessor_excluded a [3,7,6,0,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_198 : Excluded a [3,7,6,0,8,4] :=
  branch_excluded a [3,7,6,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,0,8,4,0] (by decide +kernel))
      node_199
      node_200
      (invalid_excluded a [3,7,6,0,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,4,4] (by decide +kernel))
      node_201
      (invalid_excluded a [3,7,6,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,4,8] (by decide +kernel)))

theorem node_195 : Excluded a [3,7,6,0,8] :=
  branch_excluded a [3,7,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,0,8,0] (by decide +kernel))
      node_196
      node_197
      (invalid_excluded a [3,7,6,0,8,3] (by decide +kernel))
      node_198
      (invalid_excluded a [3,7,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,8,8] (by decide +kernel)))

theorem node_192 : Excluded a [3,7,6,0] :=
  branch_excluded a [3,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,0,0] (by decide +kernel))
      node_193
      node_194
      (invalid_excluded a [3,7,6,0,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,0,7] (by decide +kernel))
      node_195)

theorem node_202 : Excluded a [3,7,6,1] :=
  source_excluded a [3,7,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_203 : Excluded a [3,7,6,2] :=
  predecessor_excluded a [3,7,6,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_204 : Excluded a [3,7,6,5] :=
  source_excluded a [3,7,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_206 : Excluded a [3,7,6,8,0] :=
  predecessor_excluded a [3,7,6,8,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_209 : Excluded a [3,7,6,8,1,0,2] :=
  source_excluded a [3,7,6,8,1,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_210 : Excluded a [3,7,6,8,1,0,4] :=
  predecessor_excluded a [3,7,6,8,1,0,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_212 : Excluded a [3,7,6,8,1,0,5,2] :=
  source_excluded a [3,7,6,8,1,0,5,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_213 : Excluded a [3,7,6,8,1,0,5,4] :=
  source_excluded a [3,7,6,8,1,0,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_211 : Excluded a [3,7,6,8,1,0,5] :=
  branch_excluded a [3,7,6,8,1,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,8,1,0,5,0] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,5,1] (by decide +kernel))
      node_212
      (invalid_excluded a [3,7,6,8,1,0,5,3] (by decide +kernel))
      node_213
      (invalid_excluded a [3,7,6,8,1,0,5,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,5,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,5,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,5,8] (by decide +kernel)))

theorem node_208 : Excluded a [3,7,6,8,1,0] :=
  branch_excluded a [3,7,6,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,1] (by decide +kernel))
      node_209
      (invalid_excluded a [3,7,6,8,1,0,3] (by decide +kernel))
      node_210
      node_211
      (invalid_excluded a [3,7,6,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,8] (by decide +kernel)))

theorem node_214 : Excluded a [3,7,6,8,1,2] :=
  source_excluded a [3,7,6,8,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_217 : Excluded a [3,7,6,8,1,4,0,2] :=
  source_excluded a [3,7,6,8,1,4,0,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_219 : Excluded a [3,7,6,8,1,4,0,5,2] :=
  predecessor_excluded a [3,7,6,8,1,4,0,5,2] 1 3 8 0 (by decide) (by decide +kernel)

theorem node_218 : Excluded a [3,7,6,8,1,4,0,5] :=
  branch_excluded a [3,7,6,8,1,4,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,8,1,4,0,5,0] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,0,5,1] (by decide +kernel))
      node_219
      (invalid_excluded a [3,7,6,8,1,4,0,5,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,0,5,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,0,5,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,0,5,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,0,5,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,0,5,8] (by decide +kernel)))

theorem node_216 : Excluded a [3,7,6,8,1,4,0] :=
  branch_excluded a [3,7,6,8,1,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,8,1,4,0,0] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,0,1] (by decide +kernel))
      node_217
      (invalid_excluded a [3,7,6,8,1,4,0,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,0,4] (by decide +kernel))
      node_218
      (invalid_excluded a [3,7,6,8,1,4,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,0,8] (by decide +kernel)))

theorem node_220 : Excluded a [3,7,6,8,1,4,2] :=
  source_excluded a [3,7,6,8,1,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_221 : Excluded a [3,7,6,8,1,4,5] :=
  predecessor_excluded a [3,7,6,8,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_215 : Excluded a [3,7,6,8,1,4] :=
  branch_excluded a [3,7,6,8,1,4] (by decide)
    (fin9_cases _
      node_216
      (invalid_excluded a [3,7,6,8,1,4,1] (by decide +kernel))
      node_220
      (invalid_excluded a [3,7,6,8,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,4] (by decide +kernel))
      node_221
      (invalid_excluded a [3,7,6,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,8] (by decide +kernel)))

theorem node_207 : Excluded a [3,7,6,8,1] :=
  branch_excluded a [3,7,6,8,1] (by decide)
    (fin9_cases _
      node_208
      (invalid_excluded a [3,7,6,8,1,1] (by decide +kernel))
      node_214
      (invalid_excluded a [3,7,6,8,1,3] (by decide +kernel))
      node_215
      (invalid_excluded a [3,7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,8] (by decide +kernel)))

theorem node_222 : Excluded a [3,7,6,8,2] :=
  predecessor_excluded a [3,7,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_205 : Excluded a [3,7,6,8] :=
  branch_excluded a [3,7,6,8] (by decide)
    (fin9_cases _
      node_206
      node_207
      node_222
      (invalid_excluded a [3,7,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,8] (by decide +kernel)))

theorem node_191 : Excluded a [3,7,6] :=
  branch_excluded a [3,7,6] (by decide)
    (fin9_cases _
      node_192
      node_202
      node_203
      (invalid_excluded a [3,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,4] (by decide +kernel))
      node_204
      (invalid_excluded a [3,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,7] (by decide +kernel))
      node_205)

theorem node_223 : Excluded a [3,7,8] :=
  predecessor_excluded a [3,7,8] 0 8 1 2 (by decide) (by decide +kernel)

theorem node_160 : Excluded a [3,7] :=
  branch_excluded a [3,7] (by decide)
    (fin9_cases _
      node_161
      node_162
      (invalid_excluded a [3,7,2] (by decide +kernel))
      (invalid_excluded a [3,7,3] (by decide +kernel))
      node_163
      node_164
      node_191
      (invalid_excluded a [3,7,7] (by decide +kernel))
      node_223)

theorem node_225 : Excluded a [3,8,0] :=
  source_excluded a [3,8,0] 2 1 0 (by decide) (by decide +kernel)

theorem node_226 : Excluded a [3,8,1] :=
  source_excluded a [3,8,1] 0 2 2 (by decide) (by decide +kernel)

theorem node_227 : Excluded a [3,8,4] :=
  source_excluded a [3,8,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_230 : Excluded a [3,8,5,0,1] :=
  predecessor_excluded a [3,8,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_231 : Excluded a [3,8,5,0,2] :=
  source_excluded a [3,8,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_232 : Excluded a [3,8,5,0,6] :=
  source_excluded a [3,8,5,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_235 : Excluded a [3,8,5,0,7,1,2] :=
  predecessor_excluded a [3,8,5,0,7,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_236 : Excluded a [3,8,5,0,7,1,4] :=
  source_excluded a [3,8,5,0,7,1,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_234 : Excluded a [3,8,5,0,7,1] :=
  branch_excluded a [3,8,5,0,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,0,7,1,0] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,1,1] (by decide +kernel))
      node_235
      (invalid_excluded a [3,8,5,0,7,1,3] (by decide +kernel))
      node_236
      (invalid_excluded a [3,8,5,0,7,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,1,8] (by decide +kernel)))

theorem node_238 : Excluded a [3,8,5,0,7,2,1] :=
  predecessor_excluded a [3,8,5,0,7,2,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_239 : Excluded a [3,8,5,0,7,2,4] :=
  source_excluded a [3,8,5,0,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_237 : Excluded a [3,8,5,0,7,2] :=
  branch_excluded a [3,8,5,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,0,7,2,0] (by decide +kernel))
      node_238
      (invalid_excluded a [3,8,5,0,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,2,3] (by decide +kernel))
      node_239
      (invalid_excluded a [3,8,5,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,2,8] (by decide +kernel)))

theorem node_240 : Excluded a [3,8,5,0,7,4] :=
  predecessor_excluded a [3,8,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_233 : Excluded a [3,8,5,0,7] :=
  branch_excluded a [3,8,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,0,7,0] (by decide +kernel))
      node_234
      node_237
      (invalid_excluded a [3,8,5,0,7,3] (by decide +kernel))
      node_240
      (invalid_excluded a [3,8,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,7,8] (by decide +kernel)))

theorem node_229 : Excluded a [3,8,5,0] :=
  branch_excluded a [3,8,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,0,0] (by decide +kernel))
      node_230
      node_231
      (invalid_excluded a [3,8,5,0,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,0,5] (by decide +kernel))
      node_232
      node_233
      (invalid_excluded a [3,8,5,0,8] (by decide +kernel)))

theorem node_241 : Excluded a [3,8,5,1] :=
  source_excluded a [3,8,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_242 : Excluded a [3,8,5,2] :=
  predecessor_excluded a [3,8,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_243 : Excluded a [3,8,5,6] :=
  predecessor_excluded a [3,8,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_246 : Excluded a [3,8,5,7,0,1] :=
  predecessor_excluded a [3,8,5,7,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_248 : Excluded a [3,8,5,7,0,2,1] :=
  predecessor_excluded a [3,8,5,7,0,2,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_249 : Excluded a [3,8,5,7,0,2,4] :=
  source_excluded a [3,8,5,7,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_247 : Excluded a [3,8,5,7,0,2] :=
  branch_excluded a [3,8,5,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,0,2,0] (by decide +kernel))
      node_248
      (invalid_excluded a [3,8,5,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,0,2,3] (by decide +kernel))
      node_249
      (invalid_excluded a [3,8,5,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,0,2,8] (by decide +kernel)))

theorem node_250 : Excluded a [3,8,5,7,0,4] :=
  predecessor_excluded a [3,8,5,7,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_245 : Excluded a [3,8,5,7,0] :=
  branch_excluded a [3,8,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,0,0] (by decide +kernel))
      node_246
      node_247
      (invalid_excluded a [3,8,5,7,0,3] (by decide +kernel))
      node_250
      (invalid_excluded a [3,8,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,0,8] (by decide +kernel)))

theorem node_254 : Excluded a [3,8,5,7,1,0,2,4] :=
  source_excluded a [3,8,5,7,1,0,2,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_256 : Excluded a [3,8,5,7,1,0,2,6,4] :=
  predecessor_excluded a [3,8,5,7,1,0,2,6,4] 2 1 8 4 (by decide) (by decide +kernel)

theorem node_255 : Excluded a [3,8,5,7,1,0,2,6] :=
  branch_excluded a [3,8,5,7,1,0,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,1,0,2,6,0] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,6,1] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,6,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,6,3] (by decide +kernel))
      node_256
      (invalid_excluded a [3,8,5,7,1,0,2,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,6,8] (by decide +kernel)))

theorem node_253 : Excluded a [3,8,5,7,1,0,2] :=
  branch_excluded a [3,8,5,7,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,3] (by decide +kernel))
      node_254
      (invalid_excluded a [3,8,5,7,1,0,2,5] (by decide +kernel))
      node_255
      (invalid_excluded a [3,8,5,7,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,8] (by decide +kernel)))

theorem node_257 : Excluded a [3,8,5,7,1,0,4] :=
  source_excluded a [3,8,5,7,1,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_252 : Excluded a [3,8,5,7,1,0] :=
  branch_excluded a [3,8,5,7,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,1] (by decide +kernel))
      node_253
      (invalid_excluded a [3,8,5,7,1,0,3] (by decide +kernel))
      node_257
      (invalid_excluded a [3,8,5,7,1,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,8] (by decide +kernel)))

theorem node_258 : Excluded a [3,8,5,7,1,2] :=
  predecessor_excluded a [3,8,5,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_259 : Excluded a [3,8,5,7,1,4] :=
  predecessor_excluded a [3,8,5,7,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_251 : Excluded a [3,8,5,7,1] :=
  branch_excluded a [3,8,5,7,1] (by decide)
    (fin9_cases _
      node_252
      (invalid_excluded a [3,8,5,7,1,1] (by decide +kernel))
      node_258
      (invalid_excluded a [3,8,5,7,1,3] (by decide +kernel))
      node_259
      (invalid_excluded a [3,8,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,8] (by decide +kernel)))

theorem node_260 : Excluded a [3,8,5,7,2] :=
  source_excluded a [3,8,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_261 : Excluded a [3,8,5,7,6] :=
  source_excluded a [3,8,5,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_244 : Excluded a [3,8,5,7] :=
  branch_excluded a [3,8,5,7] (by decide)
    (fin9_cases _
      node_245
      node_251
      node_260
      (invalid_excluded a [3,8,5,7,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,5] (by decide +kernel))
      node_261
      (invalid_excluded a [3,8,5,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,8] (by decide +kernel)))

theorem node_228 : Excluded a [3,8,5] :=
  branch_excluded a [3,8,5] (by decide)
    (fin9_cases _
      node_229
      node_241
      node_242
      (invalid_excluded a [3,8,5,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,5] (by decide +kernel))
      node_243
      node_244
      (invalid_excluded a [3,8,5,8] (by decide +kernel)))

theorem node_264 : Excluded a [3,8,6,0,1] :=
  predecessor_excluded a [3,8,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_265 : Excluded a [3,8,6,0,2] :=
  predecessor_excluded a [3,8,6,0,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_268 : Excluded a [3,8,6,0,7,1,2] :=
  predecessor_excluded a [3,8,6,0,7,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_269 : Excluded a [3,8,6,0,7,1,4] :=
  source_excluded a [3,8,6,0,7,1,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_270 : Excluded a [3,8,6,0,7,1,5] :=
  source_excluded a [3,8,6,0,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_267 : Excluded a [3,8,6,0,7,1] :=
  branch_excluded a [3,8,6,0,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,0,7,1,0] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,7,1,1] (by decide +kernel))
      node_268
      (invalid_excluded a [3,8,6,0,7,1,3] (by decide +kernel))
      node_269
      node_270
      (invalid_excluded a [3,8,6,0,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,7,1,8] (by decide +kernel)))

theorem node_271 : Excluded a [3,8,6,0,7,2] :=
  source_excluded a [3,8,6,0,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_272 : Excluded a [3,8,6,0,7,4] :=
  predecessor_excluded a [3,8,6,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_266 : Excluded a [3,8,6,0,7] :=
  branch_excluded a [3,8,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,0,7,0] (by decide +kernel))
      node_267
      node_271
      (invalid_excluded a [3,8,6,0,7,3] (by decide +kernel))
      node_272
      (invalid_excluded a [3,8,6,0,7,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,7,8] (by decide +kernel)))

theorem node_263 : Excluded a [3,8,6,0] :=
  branch_excluded a [3,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,0,0] (by decide +kernel))
      node_264
      node_265
      (invalid_excluded a [3,8,6,0,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,4] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,0,6] (by decide +kernel))
      node_266
      (invalid_excluded a [3,8,6,0,8] (by decide +kernel)))

theorem node_273 : Excluded a [3,8,6,1] :=
  source_excluded a [3,8,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_274 : Excluded a [3,8,6,2] :=
  predecessor_excluded a [3,8,6,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_275 : Excluded a [3,8,6,5] :=
  source_excluded a [3,8,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_276 : Excluded a [3,8,6,7] :=
  predecessor_excluded a [3,8,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_262 : Excluded a [3,8,6] :=
  branch_excluded a [3,8,6] (by decide)
    (fin9_cases _
      node_263
      node_273
      node_274
      (invalid_excluded a [3,8,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,4] (by decide +kernel))
      node_275
      (invalid_excluded a [3,8,6,6] (by decide +kernel))
      node_276
      (invalid_excluded a [3,8,6,8] (by decide +kernel)))

theorem node_279 : Excluded a [3,8,7,0,1] :=
  predecessor_excluded a [3,8,7,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_283 : Excluded a [3,8,7,0,2,1,4,5] :=
  predecessor_excluded a [3,8,7,0,2,1,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_285 : Excluded a [3,8,7,0,2,1,4,6,5] :=
  predecessor_excluded a [3,8,7,0,2,1,4,6,5] 2 1 8 5 (by decide) (by decide +kernel)

theorem node_284 : Excluded a [3,8,7,0,2,1,4,6] :=
  branch_excluded a [3,8,7,0,2,1,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,1,4,6,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,6,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,6,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,6,4] (by decide +kernel))
      node_285
      (invalid_excluded a [3,8,7,0,2,1,4,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,6,8] (by decide +kernel)))

theorem node_282 : Excluded a [3,8,7,0,2,1,4] :=
  branch_excluded a [3,8,7,0,2,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,1,4,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,4] (by decide +kernel))
      node_283
      node_284
      (invalid_excluded a [3,8,7,0,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,4,8] (by decide +kernel)))

theorem node_287 : Excluded a [3,8,7,0,2,1,5,4] :=
  predecessor_excluded a [3,8,7,0,2,1,5,4] 0 4 2 7 (by decide) (by decide +kernel)

theorem node_288 : Excluded a [3,8,7,0,2,1,5,6] :=
  predecessor_excluded a [3,8,7,0,2,1,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_286 : Excluded a [3,8,7,0,2,1,5] :=
  branch_excluded a [3,8,7,0,2,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,1,5,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,5,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,5,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,5,3] (by decide +kernel))
      node_287
      (invalid_excluded a [3,8,7,0,2,1,5,5] (by decide +kernel))
      node_288
      (invalid_excluded a [3,8,7,0,2,1,5,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,5,8] (by decide +kernel)))

theorem node_281 : Excluded a [3,8,7,0,2,1] :=
  branch_excluded a [3,8,7,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,3] (by decide +kernel))
      node_282
      node_286
      (invalid_excluded a [3,8,7,0,2,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,1,8] (by decide +kernel)))

theorem node_290 : Excluded a [3,8,7,0,2,4,1] :=
  predecessor_excluded a [3,8,7,0,2,4,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_291 : Excluded a [3,8,7,0,2,4,5] :=
  predecessor_excluded a [3,8,7,0,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_289 : Excluded a [3,8,7,0,2,4] :=
  branch_excluded a [3,8,7,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,4,0] (by decide +kernel))
      node_290
      (invalid_excluded a [3,8,7,0,2,4,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,4,4] (by decide +kernel))
      node_291
      (invalid_excluded a [3,8,7,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,4,8] (by decide +kernel)))

theorem node_280 : Excluded a [3,8,7,0,2] :=
  branch_excluded a [3,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,2,0] (by decide +kernel))
      node_281
      (invalid_excluded a [3,8,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,3] (by decide +kernel))
      node_289
      (invalid_excluded a [3,8,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,2,8] (by decide +kernel)))

theorem node_292 : Excluded a [3,8,7,0,6] :=
  source_excluded a [3,8,7,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_278 : Excluded a [3,8,7,0] :=
  branch_excluded a [3,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,0,0] (by decide +kernel))
      node_279
      node_280
      (invalid_excluded a [3,8,7,0,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,5] (by decide +kernel))
      node_292
      (invalid_excluded a [3,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,0,8] (by decide +kernel)))

theorem node_293 : Excluded a [3,8,7,1] :=
  source_excluded a [3,8,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_294 : Excluded a [3,8,7,2] :=
  predecessor_excluded a [3,8,7,2] 4 2 0 3 (by decide) (by decide +kernel)

theorem node_295 : Excluded a [3,8,7,5] :=
  source_excluded a [3,8,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_298 : Excluded a [3,8,7,6,0,1] :=
  predecessor_excluded a [3,8,7,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_299 : Excluded a [3,8,7,6,0,2] :=
  predecessor_excluded a [3,8,7,6,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_300 : Excluded a [3,8,7,6,0,4] :=
  source_excluded a [3,8,7,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_297 : Excluded a [3,8,7,6,0] :=
  branch_excluded a [3,8,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,6,0,0] (by decide +kernel))
      node_298
      node_299
      (invalid_excluded a [3,8,7,6,0,3] (by decide +kernel))
      node_300
      (invalid_excluded a [3,8,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,0,8] (by decide +kernel)))

theorem node_303 : Excluded a [3,8,7,6,1,0,2] :=
  source_excluded a [3,8,7,6,1,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_304 : Excluded a [3,8,7,6,1,0,4] :=
  source_excluded a [3,8,7,6,1,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_305 : Excluded a [3,8,7,6,1,0,5] :=
  predecessor_excluded a [3,8,7,6,1,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_302 : Excluded a [3,8,7,6,1,0] :=
  branch_excluded a [3,8,7,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,1] (by decide +kernel))
      node_303
      (invalid_excluded a [3,8,7,6,1,0,3] (by decide +kernel))
      node_304
      node_305
      (invalid_excluded a [3,8,7,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,8] (by decide +kernel)))

theorem node_306 : Excluded a [3,8,7,6,1,2] :=
  predecessor_excluded a [3,8,7,6,1,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_307 : Excluded a [3,8,7,6,1,4] :=
  source_excluded a [3,8,7,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_301 : Excluded a [3,8,7,6,1] :=
  branch_excluded a [3,8,7,6,1] (by decide)
    (fin9_cases _
      node_302
      (invalid_excluded a [3,8,7,6,1,1] (by decide +kernel))
      node_306
      (invalid_excluded a [3,8,7,6,1,3] (by decide +kernel))
      node_307
      (invalid_excluded a [3,8,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,8] (by decide +kernel)))

theorem node_310 : Excluded a [3,8,7,6,2,0,1] :=
  predecessor_excluded a [3,8,7,6,2,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_311 : Excluded a [3,8,7,6,2,0,4] :=
  source_excluded a [3,8,7,6,2,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_312 : Excluded a [3,8,7,6,2,0,5] :=
  predecessor_excluded a [3,8,7,6,2,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_309 : Excluded a [3,8,7,6,2,0] :=
  branch_excluded a [3,8,7,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,6,2,0,0] (by decide +kernel))
      node_310
      (invalid_excluded a [3,8,7,6,2,0,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,0,3] (by decide +kernel))
      node_311
      node_312
      (invalid_excluded a [3,8,7,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,0,8] (by decide +kernel)))

theorem node_315 : Excluded a [3,8,7,6,2,1,0,4] :=
  predecessor_excluded a [3,8,7,6,2,1,0,4] 0 4 2 7 (by decide) (by decide +kernel)

def b_317 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 8
  | 2 => 7
  | 3 => 6
  | 4 => 2
  | 5 => 1
  | 6 => 0
  | 7 => 5
  | 8 => 4
  | _ => 0

def cert_317 : LosingRegion (edgeOf a b_317) 0 :=
  losingMask a b_317 0 1210107567551607353705472
    (by decide +kernel) (by decide +kernel)

theorem node_317 : Excluded a [3,8,7,6,2,1,0,5,4] :=
  losing_excluded a [3,8,7,6,2,1,0,5,4] (by decide) b_317 (by decide +kernel) 1 0 7 cert_317 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_317 1 0 ∧ 7 ≠ 1 ∧ maskRegion 1210107567551607353705472 1 7; decide +kernel)

theorem node_316 : Excluded a [3,8,7,6,2,1,0,5] :=
  branch_excluded a [3,8,7,6,2,1,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,6,2,1,0,5,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,0,5,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,0,5,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,0,5,3] (by decide +kernel))
      node_317
      (invalid_excluded a [3,8,7,6,2,1,0,5,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,0,5,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,0,5,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,0,5,8] (by decide +kernel)))

theorem node_314 : Excluded a [3,8,7,6,2,1,0] :=
  branch_excluded a [3,8,7,6,2,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,6,2,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,0,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,0,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,0,3] (by decide +kernel))
      node_315
      node_316
      (invalid_excluded a [3,8,7,6,2,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,0,8] (by decide +kernel)))

theorem node_318 : Excluded a [3,8,7,6,2,1,4] :=
  source_excluded a [3,8,7,6,2,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_319 : Excluded a [3,8,7,6,2,1,5] :=
  predecessor_excluded a [3,8,7,6,2,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_313 : Excluded a [3,8,7,6,2,1] :=
  branch_excluded a [3,8,7,6,2,1] (by decide)
    (fin9_cases _
      node_314
      (invalid_excluded a [3,8,7,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,3] (by decide +kernel))
      node_318
      node_319
      (invalid_excluded a [3,8,7,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,8] (by decide +kernel)))

theorem node_320 : Excluded a [3,8,7,6,2,4] :=
  source_excluded a [3,8,7,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_308 : Excluded a [3,8,7,6,2] :=
  branch_excluded a [3,8,7,6,2] (by decide)
    (fin9_cases _
      node_309
      node_313
      (invalid_excluded a [3,8,7,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,3] (by decide +kernel))
      node_320
      (invalid_excluded a [3,8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,8] (by decide +kernel)))

theorem node_296 : Excluded a [3,8,7,6] :=
  branch_excluded a [3,8,7,6] (by decide)
    (fin9_cases _
      node_297
      node_301
      node_308
      (invalid_excluded a [3,8,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,8] (by decide +kernel)))

theorem node_277 : Excluded a [3,8,7] :=
  branch_excluded a [3,8,7] (by decide)
    (fin9_cases _
      node_278
      node_293
      node_294
      (invalid_excluded a [3,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,4] (by decide +kernel))
      node_295
      node_296
      (invalid_excluded a [3,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,8] (by decide +kernel)))

theorem node_224 : Excluded a [3,8] :=
  branch_excluded a [3,8] (by decide)
    (fin9_cases _
      node_225
      node_226
      (invalid_excluded a [3,8,2] (by decide +kernel))
      (invalid_excluded a [3,8,3] (by decide +kernel))
      node_227
      node_228
      node_262
      node_277
      (invalid_excluded a [3,8,8] (by decide +kernel)))

theorem node_3 : Excluded a [3] :=
  branch_excluded a [3] (by decide)
    (fin9_cases _
      node_4
      (invalid_excluded a [3,1] (by decide +kernel))
      (invalid_excluded a [3,2] (by decide +kernel))
      (invalid_excluded a [3,3] (by decide +kernel))
      node_5
      node_6
      node_80
      node_160
      node_224)

theorem node_323 : Excluded a [4,0,1] :=
  predecessor_excluded a [4,0,1] 3 1 1 2 (by decide) (by decide +kernel)

theorem node_325 : Excluded a [4,0,5,1] :=
  source_excluded a [4,0,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_326 : Excluded a [4,0,5,2] :=
  predecessor_excluded a [4,0,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_327 : Excluded a [4,0,5,6] :=
  predecessor_excluded a [4,0,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_329 : Excluded a [4,0,5,7,1] :=
  source_excluded a [4,0,5,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_330 : Excluded a [4,0,5,7,2] :=
  source_excluded a [4,0,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_331 : Excluded a [4,0,5,7,3] :=
  source_excluded a [4,0,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_332 : Excluded a [4,0,5,7,6] :=
  source_excluded a [4,0,5,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_333 : Excluded a [4,0,5,7,8] :=
  predecessor_excluded a [4,0,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_328 : Excluded a [4,0,5,7] :=
  branch_excluded a [4,0,5,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,5,7,0] (by decide +kernel))
      node_329
      node_330
      node_331
      (invalid_excluded a [4,0,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,0,5,7,5] (by decide +kernel))
      node_332
      (invalid_excluded a [4,0,5,7,7] (by decide +kernel))
      node_333)

theorem node_335 : Excluded a [4,0,5,8,1] :=
  source_excluded a [4,0,5,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_336 : Excluded a [4,0,5,8,2] :=
  source_excluded a [4,0,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_337 : Excluded a [4,0,5,8,3] :=
  source_excluded a [4,0,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_338 : Excluded a [4,0,5,8,6] :=
  source_excluded a [4,0,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_341 : Excluded a [4,0,5,8,7,1,2] :=
  predecessor_excluded a [4,0,5,8,7,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_342 : Excluded a [4,0,5,8,7,1,3] :=
  predecessor_excluded a [4,0,5,8,7,1,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_340 : Excluded a [4,0,5,8,7,1] :=
  branch_excluded a [4,0,5,8,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,5,8,7,1,0] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,1,1] (by decide +kernel))
      node_341
      node_342
      (invalid_excluded a [4,0,5,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,1,8] (by decide +kernel)))

theorem node_345 : Excluded a [4,0,5,8,7,2,1,3] :=
  source_excluded a [4,0,5,8,7,2,1,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_346 : Excluded a [4,0,5,8,7,2,1,6] :=
  predecessor_excluded a [4,0,5,8,7,2,1,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_344 : Excluded a [4,0,5,8,7,2,1] :=
  branch_excluded a [4,0,5,8,7,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,5,8,7,2,1,0] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,2,1,2] (by decide +kernel))
      node_345
      (invalid_excluded a [4,0,5,8,7,2,1,4] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,2,1,5] (by decide +kernel))
      node_346
      (invalid_excluded a [4,0,5,8,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,2,1,8] (by decide +kernel)))

theorem node_347 : Excluded a [4,0,5,8,7,2,3] :=
  predecessor_excluded a [4,0,5,8,7,2,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_343 : Excluded a [4,0,5,8,7,2] :=
  branch_excluded a [4,0,5,8,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,5,8,7,2,0] (by decide +kernel))
      node_344
      (invalid_excluded a [4,0,5,8,7,2,2] (by decide +kernel))
      node_347
      (invalid_excluded a [4,0,5,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,2,8] (by decide +kernel)))

theorem node_348 : Excluded a [4,0,5,8,7,3] :=
  source_excluded a [4,0,5,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_339 : Excluded a [4,0,5,8,7] :=
  branch_excluded a [4,0,5,8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,5,8,7,0] (by decide +kernel))
      node_340
      node_343
      node_348
      (invalid_excluded a [4,0,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,7,8] (by decide +kernel)))

theorem node_334 : Excluded a [4,0,5,8] :=
  branch_excluded a [4,0,5,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,5,8,0] (by decide +kernel))
      node_335
      node_336
      node_337
      (invalid_excluded a [4,0,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,0,5,8,5] (by decide +kernel))
      node_338
      node_339
      (invalid_excluded a [4,0,5,8,8] (by decide +kernel)))

theorem node_324 : Excluded a [4,0,5] :=
  branch_excluded a [4,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,5,0] (by decide +kernel))
      node_325
      node_326
      (invalid_excluded a [4,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,0,5,5] (by decide +kernel))
      node_327
      node_328
      node_334)

theorem node_350 : Excluded a [4,0,6,1] :=
  source_excluded a [4,0,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_352 : Excluded a [4,0,6,2,1] :=
  source_excluded a [4,0,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_353 : Excluded a [4,0,6,2,3] :=
  predecessor_excluded a [4,0,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_356 : Excluded a [4,0,6,2,7,1,3] :=
  source_excluded a [4,0,6,2,7,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_357 : Excluded a [4,0,6,2,7,1,5] :=
  source_excluded a [4,0,6,2,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_358 : Excluded a [4,0,6,2,7,1,8] :=
  source_excluded a [4,0,6,2,7,1,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_355 : Excluded a [4,0,6,2,7,1] :=
  branch_excluded a [4,0,6,2,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,2,7,1,0] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,7,1,1] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,7,1,2] (by decide +kernel))
      node_356
      (invalid_excluded a [4,0,6,2,7,1,4] (by decide +kernel))
      node_357
      (invalid_excluded a [4,0,6,2,7,1,6] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,7,1,7] (by decide +kernel))
      node_358)

theorem node_359 : Excluded a [4,0,6,2,7,3] :=
  source_excluded a [4,0,6,2,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_360 : Excluded a [4,0,6,2,7,8] :=
  predecessor_excluded a [4,0,6,2,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_354 : Excluded a [4,0,6,2,7] :=
  branch_excluded a [4,0,6,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,2,7,0] (by decide +kernel))
      node_355
      (invalid_excluded a [4,0,6,2,7,2] (by decide +kernel))
      node_359
      (invalid_excluded a [4,0,6,2,7,4] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,7,7] (by decide +kernel))
      node_360)

theorem node_363 : Excluded a [4,0,6,2,8,1,3] :=
  source_excluded a [4,0,6,2,8,1,3] 2 0 6 (by decide) (by decide +kernel)

def b_366 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 0
  | 2 => 6
  | 3 => 2
  | 4 => 8
  | 5 => 1
  | 6 => 5
  | 7 => 3
  | 8 => 7
  | _ => 0

def cert_366 : LosingRegion (edgeOf a b_366) 0 :=
  losingMask a b_366 0 1212621240531868521858048
    (by decide +kernel) (by decide +kernel)

theorem node_366 : Excluded a [4,0,6,2,8,1,5,3,7] :=
  losing_excluded a [4,0,6,2,8,1,5,3,7] (by decide) b_366 (by decide +kernel) 2 0 0 cert_366 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_366 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1212621240531868521858048 2 0; decide +kernel)

theorem node_365 : Excluded a [4,0,6,2,8,1,5,3] :=
  branch_excluded a [4,0,6,2,8,1,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,2,8,1,5,3,0] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,5,3,1] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,5,3,2] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,5,3,3] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,5,3,4] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,5,3,5] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,5,3,6] (by decide +kernel))
      node_366
      (invalid_excluded a [4,0,6,2,8,1,5,3,8] (by decide +kernel)))

theorem node_364 : Excluded a [4,0,6,2,8,1,5] :=
  branch_excluded a [4,0,6,2,8,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,2,8,1,5,0] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,5,1] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,5,2] (by decide +kernel))
      node_365
      (invalid_excluded a [4,0,6,2,8,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,5,5] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,5,6] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,5,7] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,5,8] (by decide +kernel)))

theorem node_362 : Excluded a [4,0,6,2,8,1] :=
  branch_excluded a [4,0,6,2,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,2,8,1,0] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,2] (by decide +kernel))
      node_363
      (invalid_excluded a [4,0,6,2,8,1,4] (by decide +kernel))
      node_364
      (invalid_excluded a [4,0,6,2,8,1,6] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,1,8] (by decide +kernel)))

theorem node_367 : Excluded a [4,0,6,2,8,3] :=
  source_excluded a [4,0,6,2,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_368 : Excluded a [4,0,6,2,8,7] :=
  source_excluded a [4,0,6,2,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_361 : Excluded a [4,0,6,2,8] :=
  branch_excluded a [4,0,6,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,2,8,0] (by decide +kernel))
      node_362
      (invalid_excluded a [4,0,6,2,8,2] (by decide +kernel))
      node_367
      (invalid_excluded a [4,0,6,2,8,4] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,8,6] (by decide +kernel))
      node_368
      (invalid_excluded a [4,0,6,2,8,8] (by decide +kernel)))

theorem node_351 : Excluded a [4,0,6,2] :=
  branch_excluded a [4,0,6,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,2,0] (by decide +kernel))
      node_352
      (invalid_excluded a [4,0,6,2,2] (by decide +kernel))
      node_353
      (invalid_excluded a [4,0,6,2,4] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,5] (by decide +kernel))
      (invalid_excluded a [4,0,6,2,6] (by decide +kernel))
      node_354
      node_361)

theorem node_369 : Excluded a [4,0,6,5] :=
  source_excluded a [4,0,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_370 : Excluded a [4,0,6,7] :=
  predecessor_excluded a [4,0,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_372 : Excluded a [4,0,6,8,1] :=
  source_excluded a [4,0,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_373 : Excluded a [4,0,6,8,2] :=
  predecessor_excluded a [4,0,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_376 : Excluded a [4,0,6,8,3,1,2] :=
  predecessor_excluded a [4,0,6,8,3,1,2] 0 2 5 6 (by decide) (by decide +kernel)

def b_379 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 0
  | 2 => 6
  | 3 => 8
  | 4 => 3
  | 5 => 1
  | 6 => 5
  | 7 => 2
  | 8 => 7
  | _ => 0

def cert_379 : LosingRegion (edgeOf a b_379) 0 :=
  losingMask a b_379 0 1212547435475202194015232
    (by decide +kernel) (by decide +kernel)

theorem node_379 : Excluded a [4,0,6,8,3,1,5,2,7] :=
  losing_excluded a [4,0,6,8,3,1,5,2,7] (by decide) b_379 (by decide +kernel) 2 0 3 cert_379 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_379 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1212547435475202194015232 2 3; decide +kernel)

theorem node_378 : Excluded a [4,0,6,8,3,1,5,2] :=
  branch_excluded a [4,0,6,8,3,1,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,8,3,1,5,2,0] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,5,2,1] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,5,2,2] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,5,2,3] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,5,2,4] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,5,2,5] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,5,2,6] (by decide +kernel))
      node_379
      (invalid_excluded a [4,0,6,8,3,1,5,2,8] (by decide +kernel)))

theorem node_377 : Excluded a [4,0,6,8,3,1,5] :=
  branch_excluded a [4,0,6,8,3,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,8,3,1,5,0] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,5,1] (by decide +kernel))
      node_378
      (invalid_excluded a [4,0,6,8,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,5,5] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,5,6] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,5,8] (by decide +kernel)))

theorem node_375 : Excluded a [4,0,6,8,3,1] :=
  branch_excluded a [4,0,6,8,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,8,3,1,0] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,1] (by decide +kernel))
      node_376
      (invalid_excluded a [4,0,6,8,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,4] (by decide +kernel))
      node_377
      (invalid_excluded a [4,0,6,8,3,1,6] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,1,8] (by decide +kernel)))

theorem node_380 : Excluded a [4,0,6,8,3,2] :=
  source_excluded a [4,0,6,8,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_381 : Excluded a [4,0,6,8,3,7] :=
  source_excluded a [4,0,6,8,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_374 : Excluded a [4,0,6,8,3] :=
  branch_excluded a [4,0,6,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,8,3,0] (by decide +kernel))
      node_375
      node_380
      (invalid_excluded a [4,0,6,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,4] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,3,6] (by decide +kernel))
      node_381
      (invalid_excluded a [4,0,6,8,3,8] (by decide +kernel)))

theorem node_384 : Excluded a [4,0,6,8,7,1,2] :=
  predecessor_excluded a [4,0,6,8,7,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_385 : Excluded a [4,0,6,8,7,1,3] :=
  source_excluded a [4,0,6,8,7,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_386 : Excluded a [4,0,6,8,7,1,5] :=
  source_excluded a [4,0,6,8,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_383 : Excluded a [4,0,6,8,7,1] :=
  branch_excluded a [4,0,6,8,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,8,7,1,0] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,7,1,1] (by decide +kernel))
      node_384
      node_385
      (invalid_excluded a [4,0,6,8,7,1,4] (by decide +kernel))
      node_386
      (invalid_excluded a [4,0,6,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,7,1,8] (by decide +kernel)))

theorem node_387 : Excluded a [4,0,6,8,7,2] :=
  source_excluded a [4,0,6,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_388 : Excluded a [4,0,6,8,7,3] :=
  source_excluded a [4,0,6,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_382 : Excluded a [4,0,6,8,7] :=
  branch_excluded a [4,0,6,8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,8,7,0] (by decide +kernel))
      node_383
      node_387
      node_388
      (invalid_excluded a [4,0,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,7,8] (by decide +kernel)))

theorem node_371 : Excluded a [4,0,6,8] :=
  branch_excluded a [4,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,8,0] (by decide +kernel))
      node_372
      node_373
      node_374
      (invalid_excluded a [4,0,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,0,6,8,6] (by decide +kernel))
      node_382
      (invalid_excluded a [4,0,6,8,8] (by decide +kernel)))

theorem node_349 : Excluded a [4,0,6] :=
  branch_excluded a [4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,6,0] (by decide +kernel))
      node_350
      node_351
      (invalid_excluded a [4,0,6,3] (by decide +kernel))
      (invalid_excluded a [4,0,6,4] (by decide +kernel))
      node_369
      (invalid_excluded a [4,0,6,6] (by decide +kernel))
      node_370
      node_371)

theorem node_390 : Excluded a [4,0,7,1] :=
  source_excluded a [4,0,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_392 : Excluded a [4,0,7,2,1] :=
  source_excluded a [4,0,7,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_393 : Excluded a [4,0,7,2,3] :=
  predecessor_excluded a [4,0,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_394 : Excluded a [4,0,7,2,6] :=
  source_excluded a [4,0,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_397 : Excluded a [4,0,7,2,8,1,3] :=
  source_excluded a [4,0,7,2,8,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_399 : Excluded a [4,0,7,2,8,1,5,3] :=
  source_excluded a [4,0,7,2,8,1,5,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_400 : Excluded a [4,0,7,2,8,1,5,6] :=
  predecessor_excluded a [4,0,7,2,8,1,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_398 : Excluded a [4,0,7,2,8,1,5] :=
  branch_excluded a [4,0,7,2,8,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,7,2,8,1,5,0] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,1,5,1] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,1,5,2] (by decide +kernel))
      node_399
      (invalid_excluded a [4,0,7,2,8,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,1,5,5] (by decide +kernel))
      node_400
      (invalid_excluded a [4,0,7,2,8,1,5,7] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,1,5,8] (by decide +kernel)))

theorem node_396 : Excluded a [4,0,7,2,8,1] :=
  branch_excluded a [4,0,7,2,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,7,2,8,1,0] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,1,2] (by decide +kernel))
      node_397
      (invalid_excluded a [4,0,7,2,8,1,4] (by decide +kernel))
      node_398
      (invalid_excluded a [4,0,7,2,8,1,6] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,1,8] (by decide +kernel)))

theorem node_403 : Excluded a [4,0,7,2,8,3,1,5] :=
  source_excluded a [4,0,7,2,8,3,1,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_405 : Excluded a [4,0,7,2,8,3,1,6,5] :=
  source_excluded a [4,0,7,2,8,3,1,6,5] 4 0 8 (by decide) (by decide +kernel)

theorem node_404 : Excluded a [4,0,7,2,8,3,1,6] :=
  branch_excluded a [4,0,7,2,8,3,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,7,2,8,3,1,6,0] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,1,6,1] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,1,6,2] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,1,6,3] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,1,6,4] (by decide +kernel))
      node_405
      (invalid_excluded a [4,0,7,2,8,3,1,6,6] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,1,6,7] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,1,6,8] (by decide +kernel)))

theorem node_402 : Excluded a [4,0,7,2,8,3,1] :=
  branch_excluded a [4,0,7,2,8,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,7,2,8,3,1,0] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,1,1] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,1,2] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,1,4] (by decide +kernel))
      node_403
      node_404
      (invalid_excluded a [4,0,7,2,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,1,8] (by decide +kernel)))

theorem node_407 : Excluded a [4,0,7,2,8,3,5,1] :=
  predecessor_excluded a [4,0,7,2,8,3,5,1] 2 0 7 1 (by decide) (by decide +kernel)

theorem node_408 : Excluded a [4,0,7,2,8,3,5,6] :=
  predecessor_excluded a [4,0,7,2,8,3,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_406 : Excluded a [4,0,7,2,8,3,5] :=
  branch_excluded a [4,0,7,2,8,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,7,2,8,3,5,0] (by decide +kernel))
      node_407
      (invalid_excluded a [4,0,7,2,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,5,5] (by decide +kernel))
      node_408
      (invalid_excluded a [4,0,7,2,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,5,8] (by decide +kernel)))

theorem node_401 : Excluded a [4,0,7,2,8,3] :=
  branch_excluded a [4,0,7,2,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,7,2,8,3,0] (by decide +kernel))
      node_402
      (invalid_excluded a [4,0,7,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,4] (by decide +kernel))
      node_406
      (invalid_excluded a [4,0,7,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,3,8] (by decide +kernel)))

theorem node_395 : Excluded a [4,0,7,2,8] :=
  branch_excluded a [4,0,7,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,7,2,8,0] (by decide +kernel))
      node_396
      (invalid_excluded a [4,0,7,2,8,2] (by decide +kernel))
      node_401
      (invalid_excluded a [4,0,7,2,8,4] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,5] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,8,8] (by decide +kernel)))

theorem node_391 : Excluded a [4,0,7,2] :=
  branch_excluded a [4,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,7,2,0] (by decide +kernel))
      node_392
      (invalid_excluded a [4,0,7,2,2] (by decide +kernel))
      node_393
      (invalid_excluded a [4,0,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,0,7,2,5] (by decide +kernel))
      node_394
      (invalid_excluded a [4,0,7,2,7] (by decide +kernel))
      node_395)

theorem node_409 : Excluded a [4,0,7,5] :=
  source_excluded a [4,0,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_411 : Excluded a [4,0,7,6,1] :=
  source_excluded a [4,0,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_412 : Excluded a [4,0,7,6,2] :=
  predecessor_excluded a [4,0,7,6,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_413 : Excluded a [4,0,7,6,3] :=
  predecessor_excluded a [4,0,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_416 : Excluded a [4,0,7,6,8,1,2] :=
  source_excluded a [4,0,7,6,8,1,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_417 : Excluded a [4,0,7,6,8,1,3] :=
  source_excluded a [4,0,7,6,8,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_418 : Excluded a [4,0,7,6,8,1,5] :=
  predecessor_excluded a [4,0,7,6,8,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_415 : Excluded a [4,0,7,6,8,1] :=
  branch_excluded a [4,0,7,6,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,7,6,8,1,0] (by decide +kernel))
      (invalid_excluded a [4,0,7,6,8,1,1] (by decide +kernel))
      node_416
      node_417
      (invalid_excluded a [4,0,7,6,8,1,4] (by decide +kernel))
      node_418
      (invalid_excluded a [4,0,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [4,0,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [4,0,7,6,8,1,8] (by decide +kernel)))

theorem node_419 : Excluded a [4,0,7,6,8,2] :=
  predecessor_excluded a [4,0,7,6,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_420 : Excluded a [4,0,7,6,8,3] :=
  source_excluded a [4,0,7,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_414 : Excluded a [4,0,7,6,8] :=
  branch_excluded a [4,0,7,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,7,6,8,0] (by decide +kernel))
      node_415
      node_419
      node_420
      (invalid_excluded a [4,0,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,0,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,0,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,0,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,0,7,6,8,8] (by decide +kernel)))

theorem node_410 : Excluded a [4,0,7,6] :=
  branch_excluded a [4,0,7,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,7,6,0] (by decide +kernel))
      node_411
      node_412
      node_413
      (invalid_excluded a [4,0,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,0,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,0,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,0,7,6,7] (by decide +kernel))
      node_414)

theorem node_421 : Excluded a [4,0,7,8] :=
  predecessor_excluded a [4,0,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_389 : Excluded a [4,0,7] :=
  branch_excluded a [4,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,7,0] (by decide +kernel))
      node_390
      node_391
      (invalid_excluded a [4,0,7,3] (by decide +kernel))
      (invalid_excluded a [4,0,7,4] (by decide +kernel))
      node_409
      node_410
      (invalid_excluded a [4,0,7,7] (by decide +kernel))
      node_421)

theorem node_423 : Excluded a [4,0,8,1] :=
  source_excluded a [4,0,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_425 : Excluded a [4,0,8,2,1] :=
  source_excluded a [4,0,8,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_426 : Excluded a [4,0,8,2,3] :=
  predecessor_excluded a [4,0,8,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_427 : Excluded a [4,0,8,2,6] :=
  source_excluded a [4,0,8,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_431 : Excluded a [4,0,8,2,7,1,3,5] :=
  source_excluded a [4,0,8,2,7,1,3,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_432 : Excluded a [4,0,8,2,7,1,3,6] :=
  predecessor_excluded a [4,0,8,2,7,1,3,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_430 : Excluded a [4,0,8,2,7,1,3] :=
  branch_excluded a [4,0,8,2,7,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,2,7,1,3,0] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,1,3,1] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,1,3,2] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,1,3,3] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,1,3,4] (by decide +kernel))
      node_431
      node_432
      (invalid_excluded a [4,0,8,2,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,1,3,8] (by decide +kernel)))

theorem node_433 : Excluded a [4,0,8,2,7,1,5] :=
  source_excluded a [4,0,8,2,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_429 : Excluded a [4,0,8,2,7,1] :=
  branch_excluded a [4,0,8,2,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,2,7,1,0] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,1,1] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,1,2] (by decide +kernel))
      node_430
      (invalid_excluded a [4,0,8,2,7,1,4] (by decide +kernel))
      node_433
      (invalid_excluded a [4,0,8,2,7,1,6] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,1,7] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,1,8] (by decide +kernel)))

theorem node_436 : Excluded a [4,0,8,2,7,3,1,5] :=
  source_excluded a [4,0,8,2,7,3,1,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_437 : Excluded a [4,0,8,2,7,3,1,6] :=
  predecessor_excluded a [4,0,8,2,7,3,1,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_435 : Excluded a [4,0,8,2,7,3,1] :=
  branch_excluded a [4,0,8,2,7,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,2,7,3,1,0] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,3,1,1] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,3,1,2] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,3,1,4] (by decide +kernel))
      node_436
      node_437
      (invalid_excluded a [4,0,8,2,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,3,1,8] (by decide +kernel)))

theorem node_438 : Excluded a [4,0,8,2,7,3,5] :=
  source_excluded a [4,0,8,2,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_434 : Excluded a [4,0,8,2,7,3] :=
  branch_excluded a [4,0,8,2,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,2,7,3,0] (by decide +kernel))
      node_435
      (invalid_excluded a [4,0,8,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,3,4] (by decide +kernel))
      node_438
      (invalid_excluded a [4,0,8,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,3,8] (by decide +kernel)))

theorem node_428 : Excluded a [4,0,8,2,7] :=
  branch_excluded a [4,0,8,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,2,7,0] (by decide +kernel))
      node_429
      (invalid_excluded a [4,0,8,2,7,2] (by decide +kernel))
      node_434
      (invalid_excluded a [4,0,8,2,7,4] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,5] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,6] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,7] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,7,8] (by decide +kernel)))

theorem node_424 : Excluded a [4,0,8,2] :=
  branch_excluded a [4,0,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,2,0] (by decide +kernel))
      node_425
      (invalid_excluded a [4,0,8,2,2] (by decide +kernel))
      node_426
      (invalid_excluded a [4,0,8,2,4] (by decide +kernel))
      (invalid_excluded a [4,0,8,2,5] (by decide +kernel))
      node_427
      node_428
      (invalid_excluded a [4,0,8,2,8] (by decide +kernel)))

theorem node_439 : Excluded a [4,0,8,5] :=
  source_excluded a [4,0,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_441 : Excluded a [4,0,8,6,1] :=
  source_excluded a [4,0,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_442 : Excluded a [4,0,8,6,2] :=
  predecessor_excluded a [4,0,8,6,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_443 : Excluded a [4,0,8,6,3] :=
  predecessor_excluded a [4,0,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_444 : Excluded a [4,0,8,6,7] :=
  predecessor_excluded a [4,0,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_440 : Excluded a [4,0,8,6] :=
  branch_excluded a [4,0,8,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,6,0] (by decide +kernel))
      node_441
      node_442
      node_443
      (invalid_excluded a [4,0,8,6,4] (by decide +kernel))
      (invalid_excluded a [4,0,8,6,5] (by decide +kernel))
      (invalid_excluded a [4,0,8,6,6] (by decide +kernel))
      node_444
      (invalid_excluded a [4,0,8,6,8] (by decide +kernel)))

theorem node_446 : Excluded a [4,0,8,7,1] :=
  source_excluded a [4,0,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_447 : Excluded a [4,0,8,7,2] :=
  predecessor_excluded a [4,0,8,7,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_450 : Excluded a [4,0,8,7,3,1,2] :=
  predecessor_excluded a [4,0,8,7,3,1,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_452 : Excluded a [4,0,8,7,3,1,5,2] :=
  source_excluded a [4,0,8,7,3,1,5,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_453 : Excluded a [4,0,8,7,3,1,5,6] :=
  predecessor_excluded a [4,0,8,7,3,1,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_451 : Excluded a [4,0,8,7,3,1,5] :=
  branch_excluded a [4,0,8,7,3,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,7,3,1,5,0] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,1,5,1] (by decide +kernel))
      node_452
      (invalid_excluded a [4,0,8,7,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,1,5,5] (by decide +kernel))
      node_453
      (invalid_excluded a [4,0,8,7,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,1,5,8] (by decide +kernel)))

theorem node_449 : Excluded a [4,0,8,7,3,1] :=
  branch_excluded a [4,0,8,7,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,7,3,1,0] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,1,1] (by decide +kernel))
      node_450
      (invalid_excluded a [4,0,8,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,1,4] (by decide +kernel))
      node_451
      (invalid_excluded a [4,0,8,7,3,1,6] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,1,8] (by decide +kernel)))

theorem node_456 : Excluded a [4,0,8,7,3,2,1,5] :=
  predecessor_excluded a [4,0,8,7,3,2,1,5] 0 5 3 7 (by decide) (by decide +kernel)

def b_458 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 0
  | 2 => 8
  | 3 => 7
  | 4 => 3
  | 5 => 2
  | 6 => 1
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_458 : LosingRegion (edgeOf a b_458) 0 :=
  losingMask a b_458 0 1210107572055219849135104
    (by decide +kernel) (by decide +kernel)

theorem node_458 : Excluded a [4,0,8,7,3,2,1,6,5] :=
  losing_excluded a [4,0,8,7,3,2,1,6,5] (by decide) b_458 (by decide +kernel) 2 0 7 cert_458 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_458 2 0 ∧ 7 ≠ 2 ∧ maskRegion 1210107572055219849135104 2 7; decide +kernel)

theorem node_457 : Excluded a [4,0,8,7,3,2,1,6] :=
  branch_excluded a [4,0,8,7,3,2,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,7,3,2,1,6,0] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,1,6,1] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,1,6,2] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,1,6,3] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,1,6,4] (by decide +kernel))
      node_458
      (invalid_excluded a [4,0,8,7,3,2,1,6,6] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,1,6,7] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,1,6,8] (by decide +kernel)))

theorem node_455 : Excluded a [4,0,8,7,3,2,1] :=
  branch_excluded a [4,0,8,7,3,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,7,3,2,1,0] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,1,1] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,1,2] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,1,3] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,1,4] (by decide +kernel))
      node_456
      node_457
      (invalid_excluded a [4,0,8,7,3,2,1,7] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,1,8] (by decide +kernel)))

theorem node_460 : Excluded a [4,0,8,7,3,2,5,1] :=
  predecessor_excluded a [4,0,8,7,3,2,5,1] 2 0 7 1 (by decide) (by decide +kernel)

theorem node_461 : Excluded a [4,0,8,7,3,2,5,6] :=
  predecessor_excluded a [4,0,8,7,3,2,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_459 : Excluded a [4,0,8,7,3,2,5] :=
  branch_excluded a [4,0,8,7,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,7,3,2,5,0] (by decide +kernel))
      node_460
      (invalid_excluded a [4,0,8,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,5,5] (by decide +kernel))
      node_461
      (invalid_excluded a [4,0,8,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,5,8] (by decide +kernel)))

theorem node_454 : Excluded a [4,0,8,7,3,2] :=
  branch_excluded a [4,0,8,7,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,7,3,2,0] (by decide +kernel))
      node_455
      (invalid_excluded a [4,0,8,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,4] (by decide +kernel))
      node_459
      (invalid_excluded a [4,0,8,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,2,8] (by decide +kernel)))

theorem node_448 : Excluded a [4,0,8,7,3] :=
  branch_excluded a [4,0,8,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,7,3,0] (by decide +kernel))
      node_449
      node_454
      (invalid_excluded a [4,0,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,3,8] (by decide +kernel)))

theorem node_462 : Excluded a [4,0,8,7,6] :=
  source_excluded a [4,0,8,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_445 : Excluded a [4,0,8,7] :=
  branch_excluded a [4,0,8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,7,0] (by decide +kernel))
      node_446
      node_447
      node_448
      (invalid_excluded a [4,0,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,5] (by decide +kernel))
      node_462
      (invalid_excluded a [4,0,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,0,8,7,8] (by decide +kernel)))

theorem node_422 : Excluded a [4,0,8] :=
  branch_excluded a [4,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,8,0] (by decide +kernel))
      node_423
      node_424
      (invalid_excluded a [4,0,8,3] (by decide +kernel))
      (invalid_excluded a [4,0,8,4] (by decide +kernel))
      node_439
      node_440
      node_445
      (invalid_excluded a [4,0,8,8] (by decide +kernel)))

theorem node_322 : Excluded a [4,0] :=
  branch_excluded a [4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0,0] (by decide +kernel))
      node_323
      (invalid_excluded a [4,0,2] (by decide +kernel))
      (invalid_excluded a [4,0,3] (by decide +kernel))
      (invalid_excluded a [4,0,4] (by decide +kernel))
      node_324
      node_349
      node_389
      node_422)

theorem node_463 : Excluded a [4,3] :=
  source_excluded a [4,3] 1 0 2 (by decide) (by decide +kernel)

theorem node_464 : Excluded a [4,5] :=
  predecessor_excluded a [4,5] 2 5 0 1 (by decide) (by decide +kernel)

theorem node_466 : Excluded a [4,6,0] :=
  predecessor_excluded a [4,6,0] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_468 : Excluded a [4,6,1,0] :=
  source_excluded a [4,6,1,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_469 : Excluded a [4,6,1,2] :=
  predecessor_excluded a [4,6,1,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_470 : Excluded a [4,6,1,5] :=
  source_excluded a [4,6,1,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_473 : Excluded a [4,6,1,7,0,2] :=
  source_excluded a [4,6,1,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_474 : Excluded a [4,6,1,7,0,3] :=
  predecessor_excluded a [4,6,1,7,0,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_476 : Excluded a [4,6,1,7,0,8,2] :=
  source_excluded a [4,6,1,7,0,8,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_477 : Excluded a [4,6,1,7,0,8,3] :=
  source_excluded a [4,6,1,7,0,8,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_478 : Excluded a [4,6,1,7,0,8,5] :=
  predecessor_excluded a [4,6,1,7,0,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_475 : Excluded a [4,6,1,7,0,8] :=
  branch_excluded a [4,6,1,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,7,0,8,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,0,8,1] (by decide +kernel))
      node_476
      node_477
      (invalid_excluded a [4,6,1,7,0,8,4] (by decide +kernel))
      node_478
      (invalid_excluded a [4,6,1,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,0,8,8] (by decide +kernel)))

theorem node_472 : Excluded a [4,6,1,7,0] :=
  branch_excluded a [4,6,1,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,7,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,0,1] (by decide +kernel))
      node_473
      node_474
      (invalid_excluded a [4,6,1,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,0,7] (by decide +kernel))
      node_475)

theorem node_479 : Excluded a [4,6,1,7,2] :=
  predecessor_excluded a [4,6,1,7,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_482 : Excluded a [4,6,1,7,3,0,2] :=
  source_excluded a [4,6,1,7,3,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_484 : Excluded a [4,6,1,7,3,0,5,2] :=
  branch_excluded a [4,6,1,7,3,0,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,7,3,0,5,2,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,5,2,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,5,2,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,5,2,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,5,2,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,5,2,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,5,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,5,2,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,5,2,8] (by decide +kernel)))

theorem node_483 : Excluded a [4,6,1,7,3,0,5] :=
  branch_excluded a [4,6,1,7,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,7,3,0,5,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,5,1] (by decide +kernel))
      node_484
      (invalid_excluded a [4,6,1,7,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,5,8] (by decide +kernel)))

theorem node_485 : Excluded a [4,6,1,7,3,0,8] :=
  source_excluded a [4,6,1,7,3,0,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_481 : Excluded a [4,6,1,7,3,0] :=
  branch_excluded a [4,6,1,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,7,3,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,1] (by decide +kernel))
      node_482
      (invalid_excluded a [4,6,1,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,4] (by decide +kernel))
      node_483
      (invalid_excluded a [4,6,1,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,0,7] (by decide +kernel))
      node_485)

theorem node_486 : Excluded a [4,6,1,7,3,2] :=
  source_excluded a [4,6,1,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_488 : Excluded a [4,6,1,7,3,8,0] :=
  predecessor_excluded a [4,6,1,7,3,8,0] 1 0 5 6 (by decide) (by decide +kernel)

theorem node_489 : Excluded a [4,6,1,7,3,8,2] :=
  source_excluded a [4,6,1,7,3,8,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_490 : Excluded a [4,6,1,7,3,8,5] :=
  predecessor_excluded a [4,6,1,7,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_487 : Excluded a [4,6,1,7,3,8] :=
  branch_excluded a [4,6,1,7,3,8] (by decide)
    (fin9_cases _
      node_488
      (invalid_excluded a [4,6,1,7,3,8,1] (by decide +kernel))
      node_489
      (invalid_excluded a [4,6,1,7,3,8,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,8,4] (by decide +kernel))
      node_490
      (invalid_excluded a [4,6,1,7,3,8,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,8,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,8,8] (by decide +kernel)))

theorem node_480 : Excluded a [4,6,1,7,3] :=
  branch_excluded a [4,6,1,7,3] (by decide)
    (fin9_cases _
      node_481
      (invalid_excluded a [4,6,1,7,3,1] (by decide +kernel))
      node_486
      (invalid_excluded a [4,6,1,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,7] (by decide +kernel))
      node_487)

theorem node_491 : Excluded a [4,6,1,7,8] :=
  predecessor_excluded a [4,6,1,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_471 : Excluded a [4,6,1,7] :=
  branch_excluded a [4,6,1,7] (by decide)
    (fin9_cases _
      node_472
      (invalid_excluded a [4,6,1,7,1] (by decide +kernel))
      node_479
      node_480
      (invalid_excluded a [4,6,1,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,7] (by decide +kernel))
      node_491)

theorem node_493 : Excluded a [4,6,1,8,0] :=
  predecessor_excluded a [4,6,1,8,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_494 : Excluded a [4,6,1,8,2] :=
  predecessor_excluded a [4,6,1,8,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_497 : Excluded a [4,6,1,8,3,0,2] :=
  source_excluded a [4,6,1,8,3,0,2] 1 0 6 (by decide) (by decide +kernel)

def b_500 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 1
  | 3 => 8
  | 4 => 3
  | 5 => 0
  | 6 => 5
  | 7 => 2
  | 8 => 7
  | _ => 0

def cert_500 : LosingRegion (edgeOf a b_500) 0 :=
  losingMask a b_500 0 1210181640490522682340864
    (by decide +kernel) (by decide +kernel)

theorem node_500 : Excluded a [4,6,1,8,3,0,5,2,7] :=
  losing_excluded a [4,6,1,8,3,0,5,2,7] (by decide) b_500 (by decide +kernel) 1 0 0 cert_500 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_500 1 0 ∧ 0 ≠ 1 ∧ maskRegion 1210181640490522682340864 1 0; decide +kernel)

theorem node_499 : Excluded a [4,6,1,8,3,0,5,2] :=
  branch_excluded a [4,6,1,8,3,0,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,8,3,0,5,2,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,5,2,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,5,2,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,5,2,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,5,2,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,5,2,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,5,2,6] (by decide +kernel))
      node_500
      (invalid_excluded a [4,6,1,8,3,0,5,2,8] (by decide +kernel)))

theorem node_498 : Excluded a [4,6,1,8,3,0,5] :=
  branch_excluded a [4,6,1,8,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,8,3,0,5,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,5,1] (by decide +kernel))
      node_499
      (invalid_excluded a [4,6,1,8,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,5,8] (by decide +kernel)))

theorem node_496 : Excluded a [4,6,1,8,3,0] :=
  branch_excluded a [4,6,1,8,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,8,3,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,1] (by decide +kernel))
      node_497
      (invalid_excluded a [4,6,1,8,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,4] (by decide +kernel))
      node_498
      (invalid_excluded a [4,6,1,8,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,0,8] (by decide +kernel)))

theorem node_501 : Excluded a [4,6,1,8,3,2] :=
  source_excluded a [4,6,1,8,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_502 : Excluded a [4,6,1,8,3,7] :=
  source_excluded a [4,6,1,8,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_495 : Excluded a [4,6,1,8,3] :=
  branch_excluded a [4,6,1,8,3] (by decide)
    (fin9_cases _
      node_496
      (invalid_excluded a [4,6,1,8,3,1] (by decide +kernel))
      node_501
      (invalid_excluded a [4,6,1,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,6] (by decide +kernel))
      node_502
      (invalid_excluded a [4,6,1,8,3,8] (by decide +kernel)))

theorem node_505 : Excluded a [4,6,1,8,7,0,2] :=
  source_excluded a [4,6,1,8,7,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_506 : Excluded a [4,6,1,8,7,0,3] :=
  predecessor_excluded a [4,6,1,8,7,0,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_507 : Excluded a [4,6,1,8,7,0,5] :=
  source_excluded a [4,6,1,8,7,0,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_504 : Excluded a [4,6,1,8,7,0] :=
  branch_excluded a [4,6,1,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,8,7,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,0,1] (by decide +kernel))
      node_505
      node_506
      (invalid_excluded a [4,6,1,8,7,0,4] (by decide +kernel))
      node_507
      (invalid_excluded a [4,6,1,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,0,8] (by decide +kernel)))

theorem node_508 : Excluded a [4,6,1,8,7,2] :=
  source_excluded a [4,6,1,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_512 : Excluded a [4,6,1,8,7,3,0,2,5] :=
  predecessor_excluded a [4,6,1,8,7,3,0,2,5] 0 5 3 8 (by decide) (by decide +kernel)

theorem node_511 : Excluded a [4,6,1,8,7,3,0,2] :=
  branch_excluded a [4,6,1,8,7,3,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,8,7,3,0,2,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,0,2,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,0,2,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,0,2,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,0,2,4] (by decide +kernel))
      node_512
      (invalid_excluded a [4,6,1,8,7,3,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,0,2,8] (by decide +kernel)))

theorem node_513 : Excluded a [4,6,1,8,7,3,0,5] :=
  source_excluded a [4,6,1,8,7,3,0,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_510 : Excluded a [4,6,1,8,7,3,0] :=
  branch_excluded a [4,6,1,8,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,8,7,3,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,0,1] (by decide +kernel))
      node_511
      (invalid_excluded a [4,6,1,8,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,0,4] (by decide +kernel))
      node_513
      (invalid_excluded a [4,6,1,8,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,0,8] (by decide +kernel)))

theorem node_514 : Excluded a [4,6,1,8,7,3,2] :=
  source_excluded a [4,6,1,8,7,3,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_515 : Excluded a [4,6,1,8,7,3,5] :=
  source_excluded a [4,6,1,8,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_509 : Excluded a [4,6,1,8,7,3] :=
  branch_excluded a [4,6,1,8,7,3] (by decide)
    (fin9_cases _
      node_510
      (invalid_excluded a [4,6,1,8,7,3,1] (by decide +kernel))
      node_514
      (invalid_excluded a [4,6,1,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,4] (by decide +kernel))
      node_515
      (invalid_excluded a [4,6,1,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,8] (by decide +kernel)))

theorem node_503 : Excluded a [4,6,1,8,7] :=
  branch_excluded a [4,6,1,8,7] (by decide)
    (fin9_cases _
      node_504
      (invalid_excluded a [4,6,1,8,7,1] (by decide +kernel))
      node_508
      node_509
      (invalid_excluded a [4,6,1,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,8] (by decide +kernel)))

theorem node_492 : Excluded a [4,6,1,8] :=
  branch_excluded a [4,6,1,8] (by decide)
    (fin9_cases _
      node_493
      (invalid_excluded a [4,6,1,8,1] (by decide +kernel))
      node_494
      node_495
      (invalid_excluded a [4,6,1,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,6] (by decide +kernel))
      node_503
      (invalid_excluded a [4,6,1,8,8] (by decide +kernel)))

theorem node_467 : Excluded a [4,6,1] :=
  branch_excluded a [4,6,1] (by decide)
    (fin9_cases _
      node_468
      (invalid_excluded a [4,6,1,1] (by decide +kernel))
      node_469
      (invalid_excluded a [4,6,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,4] (by decide +kernel))
      node_470
      (invalid_excluded a [4,6,1,6] (by decide +kernel))
      node_471
      node_492)

theorem node_517 : Excluded a [4,6,5,0] :=
  source_excluded a [4,6,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_518 : Excluded a [4,6,5,1] :=
  source_excluded a [4,6,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_519 : Excluded a [4,6,5,2] :=
  predecessor_excluded a [4,6,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_522 : Excluded a [4,6,5,7,0,1] :=
  source_excluded a [4,6,5,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_523 : Excluded a [4,6,5,7,0,2] :=
  source_excluded a [4,6,5,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_524 : Excluded a [4,6,5,7,0,3] :=
  source_excluded a [4,6,5,7,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_527 : Excluded a [4,6,5,7,0,8,1,2] :=
  predecessor_excluded a [4,6,5,7,0,8,1,2] 0 2 6 7 (by decide) (by decide +kernel)

def b_529 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 5
  | 3 => 7
  | 4 => 0
  | 5 => 8
  | 6 => 1
  | 7 => 3
  | 8 => 2
  | _ => 0

def cert_529 : LosingRegion (edgeOf a b_529) 0 :=
  losingMask a b_529 0 1210110019745648638794752
    (by decide +kernel) (by decide +kernel)

theorem node_529 : Excluded a [4,6,5,7,0,8,1,3,2] :=
  losing_excluded a [4,6,5,7,0,8,1,3,2] (by decide) b_529 (by decide +kernel) 1 0 2 cert_529 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_529 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1210110019745648638794752 1 2; decide +kernel)

theorem node_528 : Excluded a [4,6,5,7,0,8,1,3] :=
  branch_excluded a [4,6,5,7,0,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,5,7,0,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,1,3,1] (by decide +kernel))
      node_529
      (invalid_excluded a [4,6,5,7,0,8,1,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,1,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,1,3,8] (by decide +kernel)))

theorem node_526 : Excluded a [4,6,5,7,0,8,1] :=
  branch_excluded a [4,6,5,7,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,5,7,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,1,1] (by decide +kernel))
      node_527
      node_528
      (invalid_excluded a [4,6,5,7,0,8,1,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,1,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,1,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,1,8] (by decide +kernel)))

theorem node_530 : Excluded a [4,6,5,7,0,8,2] :=
  source_excluded a [4,6,5,7,0,8,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_531 : Excluded a [4,6,5,7,0,8,3] :=
  source_excluded a [4,6,5,7,0,8,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_525 : Excluded a [4,6,5,7,0,8] :=
  branch_excluded a [4,6,5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,5,7,0,8,0] (by decide +kernel))
      node_526
      node_530
      node_531
      (invalid_excluded a [4,6,5,7,0,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,8,8] (by decide +kernel)))

theorem node_521 : Excluded a [4,6,5,7,0] :=
  branch_excluded a [4,6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,5,7,0,0] (by decide +kernel))
      node_522
      node_523
      node_524
      (invalid_excluded a [4,6,5,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,0,7] (by decide +kernel))
      node_525)

theorem node_532 : Excluded a [4,6,5,7,1] :=
  source_excluded a [4,6,5,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_533 : Excluded a [4,6,5,7,2] :=
  source_excluded a [4,6,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_534 : Excluded a [4,6,5,7,3] :=
  source_excluded a [4,6,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_535 : Excluded a [4,6,5,7,8] :=
  predecessor_excluded a [4,6,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_520 : Excluded a [4,6,5,7] :=
  branch_excluded a [4,6,5,7] (by decide)
    (fin9_cases _
      node_521
      node_532
      node_533
      node_534
      (invalid_excluded a [4,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,7] (by decide +kernel))
      node_535)

theorem node_537 : Excluded a [4,6,5,8,0] :=
  predecessor_excluded a [4,6,5,8,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_538 : Excluded a [4,6,5,8,1] :=
  source_excluded a [4,6,5,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_539 : Excluded a [4,6,5,8,2] :=
  source_excluded a [4,6,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_540 : Excluded a [4,6,5,8,3] :=
  source_excluded a [4,6,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_543 : Excluded a [4,6,5,8,7,0,1] :=
  predecessor_excluded a [4,6,5,8,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_544 : Excluded a [4,6,5,8,7,0,2] :=
  source_excluded a [4,6,5,8,7,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_545 : Excluded a [4,6,5,8,7,0,3] :=
  predecessor_excluded a [4,6,5,8,7,0,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_542 : Excluded a [4,6,5,8,7,0] :=
  branch_excluded a [4,6,5,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,5,8,7,0,0] (by decide +kernel))
      node_543
      node_544
      node_545
      (invalid_excluded a [4,6,5,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,0,8] (by decide +kernel)))

theorem node_546 : Excluded a [4,6,5,8,7,1] :=
  source_excluded a [4,6,5,8,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_547 : Excluded a [4,6,5,8,7,2] :=
  source_excluded a [4,6,5,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_548 : Excluded a [4,6,5,8,7,3] :=
  source_excluded a [4,6,5,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_541 : Excluded a [4,6,5,8,7] :=
  branch_excluded a [4,6,5,8,7] (by decide)
    (fin9_cases _
      node_542
      node_546
      node_547
      node_548
      (invalid_excluded a [4,6,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,8] (by decide +kernel)))

theorem node_536 : Excluded a [4,6,5,8] :=
  branch_excluded a [4,6,5,8] (by decide)
    (fin9_cases _
      node_537
      node_538
      node_539
      node_540
      (invalid_excluded a [4,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,6] (by decide +kernel))
      node_541
      (invalid_excluded a [4,6,5,8,8] (by decide +kernel)))

theorem node_516 : Excluded a [4,6,5] :=
  branch_excluded a [4,6,5] (by decide)
    (fin9_cases _
      node_517
      node_518
      node_519
      (invalid_excluded a [4,6,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,6] (by decide +kernel))
      node_520
      node_536)

theorem node_549 : Excluded a [4,6,7] :=
  predecessor_excluded a [4,6,7] 0 7 1 2 (by decide) (by decide +kernel)

theorem node_551 : Excluded a [4,6,8,0] :=
  source_excluded a [4,6,8,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_552 : Excluded a [4,6,8,1] :=
  source_excluded a [4,6,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_555 : Excluded a [4,6,8,2,0,1] :=
  source_excluded a [4,6,8,2,0,1] 5 0 1 (by decide) (by decide +kernel)

def b_559 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 8
  | 3 => 2
  | 4 => 0
  | 5 => 3
  | 6 => 1
  | 7 => 5
  | 8 => 7
  | _ => 0

def cert_559 : LosingRegion (edgeOf a b_559) 0 :=
  losingMask a b_559 0 1210144711395790703041536
    (by decide +kernel) (by decide +kernel)

theorem node_559 : Excluded a [4,6,8,2,0,3,1,5,7] :=
  losing_excluded a [4,6,8,2,0,3,1,5,7] (by decide) b_559 (by decide +kernel) 1 0 2 cert_559 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_559 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1210144711395790703041536 1 2; decide +kernel)

theorem node_558 : Excluded a [4,6,8,2,0,3,1,5] :=
  branch_excluded a [4,6,8,2,0,3,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,2,0,3,1,5,0] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,1,5,1] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,1,5,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,1,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,1,5,6] (by decide +kernel))
      node_559
      (invalid_excluded a [4,6,8,2,0,3,1,5,8] (by decide +kernel)))

theorem node_557 : Excluded a [4,6,8,2,0,3,1] :=
  branch_excluded a [4,6,8,2,0,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,2,0,3,1,0] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,1,1] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,1,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,1,4] (by decide +kernel))
      node_558
      (invalid_excluded a [4,6,8,2,0,3,1,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,1,8] (by decide +kernel)))

theorem node_562 : Excluded a [4,6,8,2,0,3,5,1,7] :=
  predecessor_excluded a [4,6,8,2,0,3,5,1,7] 2 1 8 7 (by decide) (by decide +kernel)

theorem node_561 : Excluded a [4,6,8,2,0,3,5,1] :=
  branch_excluded a [4,6,8,2,0,3,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,2,0,3,5,1,0] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,5,1,1] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,5,1,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,5,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,5,1,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,5,1,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,5,1,6] (by decide +kernel))
      node_562
      (invalid_excluded a [4,6,8,2,0,3,5,1,8] (by decide +kernel)))

theorem node_560 : Excluded a [4,6,8,2,0,3,5] :=
  branch_excluded a [4,6,8,2,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,2,0,3,5,0] (by decide +kernel))
      node_561
      (invalid_excluded a [4,6,8,2,0,3,5,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,5,8] (by decide +kernel)))

theorem node_556 : Excluded a [4,6,8,2,0,3] :=
  branch_excluded a [4,6,8,2,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,2,0,3,0] (by decide +kernel))
      node_557
      (invalid_excluded a [4,6,8,2,0,3,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,4] (by decide +kernel))
      node_560
      (invalid_excluded a [4,6,8,2,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,3,8] (by decide +kernel)))

theorem node_563 : Excluded a [4,6,8,2,0,7] :=
  source_excluded a [4,6,8,2,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_554 : Excluded a [4,6,8,2,0] :=
  branch_excluded a [4,6,8,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,2,0,0] (by decide +kernel))
      node_555
      (invalid_excluded a [4,6,8,2,0,2] (by decide +kernel))
      node_556
      (invalid_excluded a [4,6,8,2,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,0,6] (by decide +kernel))
      node_563
      (invalid_excluded a [4,6,8,2,0,8] (by decide +kernel)))

theorem node_564 : Excluded a [4,6,8,2,1] :=
  source_excluded a [4,6,8,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_565 : Excluded a [4,6,8,2,3] :=
  predecessor_excluded a [4,6,8,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_568 : Excluded a [4,6,8,2,7,0,1] :=
  predecessor_excluded a [4,6,8,2,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_569 : Excluded a [4,6,8,2,7,0,3] :=
  predecessor_excluded a [4,6,8,2,7,0,3] 0 3 1 6 (by decide) (by decide +kernel)

theorem node_570 : Excluded a [4,6,8,2,7,0,5] :=
  source_excluded a [4,6,8,2,7,0,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_567 : Excluded a [4,6,8,2,7,0] :=
  branch_excluded a [4,6,8,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,2,7,0,0] (by decide +kernel))
      node_568
      (invalid_excluded a [4,6,8,2,7,0,2] (by decide +kernel))
      node_569
      (invalid_excluded a [4,6,8,2,7,0,4] (by decide +kernel))
      node_570
      (invalid_excluded a [4,6,8,2,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,0,8] (by decide +kernel)))

theorem node_571 : Excluded a [4,6,8,2,7,1] :=
  source_excluded a [4,6,8,2,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_574 : Excluded a [4,6,8,2,7,3,0,1] :=
  predecessor_excluded a [4,6,8,2,7,3,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_575 : Excluded a [4,6,8,2,7,3,0,5] :=
  source_excluded a [4,6,8,2,7,3,0,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_573 : Excluded a [4,6,8,2,7,3,0] :=
  branch_excluded a [4,6,8,2,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,2,7,3,0,0] (by decide +kernel))
      node_574
      (invalid_excluded a [4,6,8,2,7,3,0,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,0,4] (by decide +kernel))
      node_575
      (invalid_excluded a [4,6,8,2,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,0,8] (by decide +kernel)))

theorem node_577 : Excluded a [4,6,8,2,7,3,1,0] :=
  source_excluded a [4,6,8,2,7,3,1,0] 7 1 8 (by decide) (by decide +kernel)

theorem node_578 : Excluded a [4,6,8,2,7,3,1,5] :=
  source_excluded a [4,6,8,2,7,3,1,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_576 : Excluded a [4,6,8,2,7,3,1] :=
  branch_excluded a [4,6,8,2,7,3,1] (by decide)
    (fin9_cases _
      node_577
      (invalid_excluded a [4,6,8,2,7,3,1,1] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,1,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,1,4] (by decide +kernel))
      node_578
      (invalid_excluded a [4,6,8,2,7,3,1,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,1,8] (by decide +kernel)))

theorem node_579 : Excluded a [4,6,8,2,7,3,5] :=
  source_excluded a [4,6,8,2,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_572 : Excluded a [4,6,8,2,7,3] :=
  branch_excluded a [4,6,8,2,7,3] (by decide)
    (fin9_cases _
      node_573
      node_576
      (invalid_excluded a [4,6,8,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,4] (by decide +kernel))
      node_579
      (invalid_excluded a [4,6,8,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,3,8] (by decide +kernel)))

theorem node_566 : Excluded a [4,6,8,2,7] :=
  branch_excluded a [4,6,8,2,7] (by decide)
    (fin9_cases _
      node_567
      node_571
      (invalid_excluded a [4,6,8,2,7,2] (by decide +kernel))
      node_572
      (invalid_excluded a [4,6,8,2,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,7,8] (by decide +kernel)))

theorem node_553 : Excluded a [4,6,8,2] :=
  branch_excluded a [4,6,8,2] (by decide)
    (fin9_cases _
      node_554
      node_564
      (invalid_excluded a [4,6,8,2,2] (by decide +kernel))
      node_565
      (invalid_excluded a [4,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,2,6] (by decide +kernel))
      node_566
      (invalid_excluded a [4,6,8,2,8] (by decide +kernel)))

theorem node_580 : Excluded a [4,6,8,5] :=
  source_excluded a [4,6,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_583 : Excluded a [4,6,8,7,0,1] :=
  source_excluded a [4,6,8,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_584 : Excluded a [4,6,8,7,0,2] :=
  source_excluded a [4,6,8,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_585 : Excluded a [4,6,8,7,0,3] :=
  predecessor_excluded a [4,6,8,7,0,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_582 : Excluded a [4,6,8,7,0] :=
  branch_excluded a [4,6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,7,0,0] (by decide +kernel))
      node_583
      node_584
      node_585
      (invalid_excluded a [4,6,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,0,8] (by decide +kernel)))

theorem node_586 : Excluded a [4,6,8,7,1] :=
  source_excluded a [4,6,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_587 : Excluded a [4,6,8,7,2] :=
  predecessor_excluded a [4,6,8,7,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_590 : Excluded a [4,6,8,7,3,0,1] :=
  predecessor_excluded a [4,6,8,7,3,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_591 : Excluded a [4,6,8,7,3,0,2] :=
  source_excluded a [4,6,8,7,3,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_594 : Excluded a [4,6,8,7,3,0,5,1,2] :=
  predecessor_excluded a [4,6,8,7,3,0,5,1,2] 0 2 7 8 (by decide) (by decide +kernel)

theorem node_593 : Excluded a [4,6,8,7,3,0,5,1] :=
  branch_excluded a [4,6,8,7,3,0,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,7,3,0,5,1,0] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,1,1] (by decide +kernel))
      node_594
      (invalid_excluded a [4,6,8,7,3,0,5,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,1,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,1,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,1,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,1,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,1,8] (by decide +kernel)))

theorem node_595 : Excluded a [4,6,8,7,3,0,5,2] :=
  source_excluded a [4,6,8,7,3,0,5,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_592 : Excluded a [4,6,8,7,3,0,5] :=
  branch_excluded a [4,6,8,7,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,7,3,0,5,0] (by decide +kernel))
      node_593
      node_595
      (invalid_excluded a [4,6,8,7,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,5,8] (by decide +kernel)))

theorem node_589 : Excluded a [4,6,8,7,3,0] :=
  branch_excluded a [4,6,8,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,7,3,0,0] (by decide +kernel))
      node_590
      node_591
      (invalid_excluded a [4,6,8,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,4] (by decide +kernel))
      node_592
      (invalid_excluded a [4,6,8,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,0,8] (by decide +kernel)))

theorem node_596 : Excluded a [4,6,8,7,3,1] :=
  source_excluded a [4,6,8,7,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_597 : Excluded a [4,6,8,7,3,2] :=
  source_excluded a [4,6,8,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_588 : Excluded a [4,6,8,7,3] :=
  branch_excluded a [4,6,8,7,3] (by decide)
    (fin9_cases _
      node_589
      node_596
      node_597
      (invalid_excluded a [4,6,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,8] (by decide +kernel)))

theorem node_581 : Excluded a [4,6,8,7] :=
  branch_excluded a [4,6,8,7] (by decide)
    (fin9_cases _
      node_582
      node_586
      node_587
      node_588
      (invalid_excluded a [4,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,8] (by decide +kernel)))

theorem node_550 : Excluded a [4,6,8] :=
  branch_excluded a [4,6,8] (by decide)
    (fin9_cases _
      node_551
      node_552
      node_553
      (invalid_excluded a [4,6,8,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,4] (by decide +kernel))
      node_580
      (invalid_excluded a [4,6,8,6] (by decide +kernel))
      node_581
      (invalid_excluded a [4,6,8,8] (by decide +kernel)))

theorem node_465 : Excluded a [4,6] :=
  branch_excluded a [4,6] (by decide)
    (fin9_cases _
      node_466
      node_467
      (invalid_excluded a [4,6,2] (by decide +kernel))
      (invalid_excluded a [4,6,3] (by decide +kernel))
      (invalid_excluded a [4,6,4] (by decide +kernel))
      node_516
      (invalid_excluded a [4,6,6] (by decide +kernel))
      node_549
      node_550)

theorem node_599 : Excluded a [4,7,0] :=
  predecessor_excluded a [4,7,0] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_601 : Excluded a [4,7,1,0] :=
  source_excluded a [4,7,1,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_602 : Excluded a [4,7,1,2] :=
  predecessor_excluded a [4,7,1,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_603 : Excluded a [4,7,1,5] :=
  source_excluded a [4,7,1,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_607 : Excluded a [4,7,1,6,0,2,3] :=
  predecessor_excluded a [4,7,1,6,0,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_608 : Excluded a [4,7,1,6,0,2,5] :=
  predecessor_excluded a [4,7,1,6,0,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_609 : Excluded a [4,7,1,6,0,2,8] :=
  source_excluded a [4,7,1,6,0,2,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_606 : Excluded a [4,7,1,6,0,2] :=
  branch_excluded a [4,7,1,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,0,2,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,0,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,0,2,2] (by decide +kernel))
      node_607
      (invalid_excluded a [4,7,1,6,0,2,4] (by decide +kernel))
      node_608
      (invalid_excluded a [4,7,1,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,0,2,7] (by decide +kernel))
      node_609)

theorem node_610 : Excluded a [4,7,1,6,0,3] :=
  source_excluded a [4,7,1,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_612 : Excluded a [4,7,1,6,0,8,2] :=
  source_excluded a [4,7,1,6,0,8,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_614 : Excluded a [4,7,1,6,0,8,3,2] :=
  source_excluded a [4,7,1,6,0,8,3,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_615 : Excluded a [4,7,1,6,0,8,3,5] :=
  source_excluded a [4,7,1,6,0,8,3,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_613 : Excluded a [4,7,1,6,0,8,3] :=
  branch_excluded a [4,7,1,6,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,0,8,3,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,0,8,3,1] (by decide +kernel))
      node_614
      (invalid_excluded a [4,7,1,6,0,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,0,8,3,4] (by decide +kernel))
      node_615
      (invalid_excluded a [4,7,1,6,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,0,8,3,8] (by decide +kernel)))

theorem node_616 : Excluded a [4,7,1,6,0,8,5] :=
  predecessor_excluded a [4,7,1,6,0,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_611 : Excluded a [4,7,1,6,0,8] :=
  branch_excluded a [4,7,1,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,0,8,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,0,8,1] (by decide +kernel))
      node_612
      node_613
      (invalid_excluded a [4,7,1,6,0,8,4] (by decide +kernel))
      node_616
      (invalid_excluded a [4,7,1,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,0,8,8] (by decide +kernel)))

theorem node_605 : Excluded a [4,7,1,6,0] :=
  branch_excluded a [4,7,1,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,0,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,0,1] (by decide +kernel))
      node_606
      node_610
      (invalid_excluded a [4,7,1,6,0,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,0,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,0,7] (by decide +kernel))
      node_611)

theorem node_617 : Excluded a [4,7,1,6,2] :=
  predecessor_excluded a [4,7,1,6,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_618 : Excluded a [4,7,1,6,3] :=
  predecessor_excluded a [4,7,1,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_620 : Excluded a [4,7,1,6,8,0] :=
  predecessor_excluded a [4,7,1,6,8,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_623 : Excluded a [4,7,1,6,8,2,0,3] :=
  predecessor_excluded a [4,7,1,6,8,2,0,3] 0 3 1 7 (by decide) (by decide +kernel)

theorem node_624 : Excluded a [4,7,1,6,8,2,0,5] :=
  source_excluded a [4,7,1,6,8,2,0,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_622 : Excluded a [4,7,1,6,8,2,0] :=
  branch_excluded a [4,7,1,6,8,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,8,2,0,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,0,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,0,2] (by decide +kernel))
      node_623
      (invalid_excluded a [4,7,1,6,8,2,0,4] (by decide +kernel))
      node_624
      (invalid_excluded a [4,7,1,6,8,2,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,0,8] (by decide +kernel)))

theorem node_625 : Excluded a [4,7,1,6,8,2,3] :=
  predecessor_excluded a [4,7,1,6,8,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_626 : Excluded a [4,7,1,6,8,2,5] :=
  predecessor_excluded a [4,7,1,6,8,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_621 : Excluded a [4,7,1,6,8,2] :=
  branch_excluded a [4,7,1,6,8,2] (by decide)
    (fin9_cases _
      node_622
      (invalid_excluded a [4,7,1,6,8,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,2] (by decide +kernel))
      node_625
      (invalid_excluded a [4,7,1,6,8,2,4] (by decide +kernel))
      node_626
      (invalid_excluded a [4,7,1,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,8] (by decide +kernel)))

theorem node_627 : Excluded a [4,7,1,6,8,3] :=
  source_excluded a [4,7,1,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_619 : Excluded a [4,7,1,6,8] :=
  branch_excluded a [4,7,1,6,8] (by decide)
    (fin9_cases _
      node_620
      (invalid_excluded a [4,7,1,6,8,1] (by decide +kernel))
      node_621
      node_627
      (invalid_excluded a [4,7,1,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,8] (by decide +kernel)))

theorem node_604 : Excluded a [4,7,1,6] :=
  branch_excluded a [4,7,1,6] (by decide)
    (fin9_cases _
      node_605
      (invalid_excluded a [4,7,1,6,1] (by decide +kernel))
      node_617
      node_618
      (invalid_excluded a [4,7,1,6,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,7] (by decide +kernel))
      node_619)

theorem node_629 : Excluded a [4,7,1,8,0] :=
  predecessor_excluded a [4,7,1,8,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_630 : Excluded a [4,7,1,8,2] :=
  predecessor_excluded a [4,7,1,8,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_633 : Excluded a [4,7,1,8,3,0,2] :=
  source_excluded a [4,7,1,8,3,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_635 : Excluded a [4,7,1,8,3,0,5,2] :=
  source_excluded a [4,7,1,8,3,0,5,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_636 : Excluded a [4,7,1,8,3,0,5,6] :=
  predecessor_excluded a [4,7,1,8,3,0,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_634 : Excluded a [4,7,1,8,3,0,5] :=
  branch_excluded a [4,7,1,8,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,8,3,0,5,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,5,1] (by decide +kernel))
      node_635
      (invalid_excluded a [4,7,1,8,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,5,5] (by decide +kernel))
      node_636
      (invalid_excluded a [4,7,1,8,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,5,8] (by decide +kernel)))

theorem node_632 : Excluded a [4,7,1,8,3,0] :=
  branch_excluded a [4,7,1,8,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,8,3,0,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,1] (by decide +kernel))
      node_633
      (invalid_excluded a [4,7,1,8,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,4] (by decide +kernel))
      node_634
      (invalid_excluded a [4,7,1,8,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,8] (by decide +kernel)))

theorem node_640 : Excluded a [4,7,1,8,3,2,0,5,6] :=
  source_excluded a [4,7,1,8,3,2,0,5,6] 8 1 6 (by decide) (by decide +kernel)

theorem node_639 : Excluded a [4,7,1,8,3,2,0,5] :=
  branch_excluded a [4,7,1,8,3,2,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,8,3,2,0,5,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,0,5,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,0,5,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,0,5,5] (by decide +kernel))
      node_640
      (invalid_excluded a [4,7,1,8,3,2,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,0,5,8] (by decide +kernel)))

theorem node_641 : Excluded a [4,7,1,8,3,2,0,6] :=
  predecessor_excluded a [4,7,1,8,3,2,0,6] 1 0 7 6 (by decide) (by decide +kernel)

theorem node_638 : Excluded a [4,7,1,8,3,2,0] :=
  branch_excluded a [4,7,1,8,3,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,8,3,2,0,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,0,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,0,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,0,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,0,4] (by decide +kernel))
      node_639
      node_641
      (invalid_excluded a [4,7,1,8,3,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,0,8] (by decide +kernel)))

theorem node_643 : Excluded a [4,7,1,8,3,2,5,0] :=
  source_excluded a [4,7,1,8,3,2,5,0] 7 1 8 (by decide) (by decide +kernel)

theorem node_644 : Excluded a [4,7,1,8,3,2,5,6] :=
  predecessor_excluded a [4,7,1,8,3,2,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_642 : Excluded a [4,7,1,8,3,2,5] :=
  branch_excluded a [4,7,1,8,3,2,5] (by decide)
    (fin9_cases _
      node_643
      (invalid_excluded a [4,7,1,8,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,5,5] (by decide +kernel))
      node_644
      (invalid_excluded a [4,7,1,8,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,5,8] (by decide +kernel)))

theorem node_637 : Excluded a [4,7,1,8,3,2] :=
  branch_excluded a [4,7,1,8,3,2] (by decide)
    (fin9_cases _
      node_638
      (invalid_excluded a [4,7,1,8,3,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,4] (by decide +kernel))
      node_642
      (invalid_excluded a [4,7,1,8,3,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,8] (by decide +kernel)))

theorem node_631 : Excluded a [4,7,1,8,3] :=
  branch_excluded a [4,7,1,8,3] (by decide)
    (fin9_cases _
      node_632
      (invalid_excluded a [4,7,1,8,3,1] (by decide +kernel))
      node_637
      (invalid_excluded a [4,7,1,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,8] (by decide +kernel)))

theorem node_645 : Excluded a [4,7,1,8,6] :=
  source_excluded a [4,7,1,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_628 : Excluded a [4,7,1,8] :=
  branch_excluded a [4,7,1,8] (by decide)
    (fin9_cases _
      node_629
      (invalid_excluded a [4,7,1,8,1] (by decide +kernel))
      node_630
      node_631
      (invalid_excluded a [4,7,1,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,5] (by decide +kernel))
      node_645
      (invalid_excluded a [4,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,8] (by decide +kernel)))

theorem node_600 : Excluded a [4,7,1] :=
  branch_excluded a [4,7,1] (by decide)
    (fin9_cases _
      node_601
      (invalid_excluded a [4,7,1,1] (by decide +kernel))
      node_602
      (invalid_excluded a [4,7,1,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,4] (by decide +kernel))
      node_603
      node_604
      (invalid_excluded a [4,7,1,7] (by decide +kernel))
      node_628)

theorem node_647 : Excluded a [4,7,5,0] :=
  source_excluded a [4,7,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_648 : Excluded a [4,7,5,1] :=
  source_excluded a [4,7,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_649 : Excluded a [4,7,5,2] :=
  predecessor_excluded a [4,7,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_650 : Excluded a [4,7,5,6] :=
  predecessor_excluded a [4,7,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_652 : Excluded a [4,7,5,8,0] :=
  predecessor_excluded a [4,7,5,8,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_653 : Excluded a [4,7,5,8,1] :=
  source_excluded a [4,7,5,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_654 : Excluded a [4,7,5,8,2] :=
  source_excluded a [4,7,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_655 : Excluded a [4,7,5,8,3] :=
  source_excluded a [4,7,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_656 : Excluded a [4,7,5,8,6] :=
  source_excluded a [4,7,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_651 : Excluded a [4,7,5,8] :=
  branch_excluded a [4,7,5,8] (by decide)
    (fin9_cases _
      node_652
      node_653
      node_654
      node_655
      (invalid_excluded a [4,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,5] (by decide +kernel))
      node_656
      (invalid_excluded a [4,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,8] (by decide +kernel)))

theorem node_646 : Excluded a [4,7,5] :=
  branch_excluded a [4,7,5] (by decide)
    (fin9_cases _
      node_647
      node_648
      node_649
      (invalid_excluded a [4,7,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,5] (by decide +kernel))
      node_650
      (invalid_excluded a [4,7,5,7] (by decide +kernel))
      node_651)

theorem node_658 : Excluded a [4,7,6,0] :=
  source_excluded a [4,7,6,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_659 : Excluded a [4,7,6,1] :=
  source_excluded a [4,7,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_662 : Excluded a [4,7,6,2,0,1] :=
  predecessor_excluded a [4,7,6,2,0,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_663 : Excluded a [4,7,6,2,0,3] :=
  source_excluded a [4,7,6,2,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_665 : Excluded a [4,7,6,2,0,8,1] :=
  source_excluded a [4,7,6,2,0,8,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_666 : Excluded a [4,7,6,2,0,8,3] :=
  source_excluded a [4,7,6,2,0,8,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_667 : Excluded a [4,7,6,2,0,8,5] :=
  predecessor_excluded a [4,7,6,2,0,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_664 : Excluded a [4,7,6,2,0,8] :=
  branch_excluded a [4,7,6,2,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,2,0,8,0] (by decide +kernel))
      node_665
      (invalid_excluded a [4,7,6,2,0,8,2] (by decide +kernel))
      node_666
      (invalid_excluded a [4,7,6,2,0,8,4] (by decide +kernel))
      node_667
      (invalid_excluded a [4,7,6,2,0,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,0,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,0,8,8] (by decide +kernel)))

theorem node_661 : Excluded a [4,7,6,2,0] :=
  branch_excluded a [4,7,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,2,0,0] (by decide +kernel))
      node_662
      (invalid_excluded a [4,7,6,2,0,2] (by decide +kernel))
      node_663
      (invalid_excluded a [4,7,6,2,0,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,0,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,0,7] (by decide +kernel))
      node_664)

theorem node_668 : Excluded a [4,7,6,2,1] :=
  source_excluded a [4,7,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_669 : Excluded a [4,7,6,2,3] :=
  predecessor_excluded a [4,7,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_671 : Excluded a [4,7,6,2,8,0] :=
  predecessor_excluded a [4,7,6,2,8,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_672 : Excluded a [4,7,6,2,8,1] :=
  predecessor_excluded a [4,7,6,2,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_673 : Excluded a [4,7,6,2,8,3] :=
  source_excluded a [4,7,6,2,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_670 : Excluded a [4,7,6,2,8] :=
  branch_excluded a [4,7,6,2,8] (by decide)
    (fin9_cases _
      node_671
      node_672
      (invalid_excluded a [4,7,6,2,8,2] (by decide +kernel))
      node_673
      (invalid_excluded a [4,7,6,2,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,8] (by decide +kernel)))

theorem node_660 : Excluded a [4,7,6,2] :=
  branch_excluded a [4,7,6,2] (by decide)
    (fin9_cases _
      node_661
      node_668
      (invalid_excluded a [4,7,6,2,2] (by decide +kernel))
      node_669
      (invalid_excluded a [4,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,7] (by decide +kernel))
      node_670)

theorem node_674 : Excluded a [4,7,6,5] :=
  source_excluded a [4,7,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_676 : Excluded a [4,7,6,8,0] :=
  predecessor_excluded a [4,7,6,8,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_677 : Excluded a [4,7,6,8,1] :=
  source_excluded a [4,7,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_678 : Excluded a [4,7,6,8,2] :=
  predecessor_excluded a [4,7,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_681 : Excluded a [4,7,6,8,3,0,1] :=
  source_excluded a [4,7,6,8,3,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_682 : Excluded a [4,7,6,8,3,0,2] :=
  source_excluded a [4,7,6,8,3,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_685 : Excluded a [4,7,6,8,3,0,5,1,2] :=
  predecessor_excluded a [4,7,6,8,3,0,5,1,2] 0 2 7 8 (by decide) (by decide +kernel)

theorem node_684 : Excluded a [4,7,6,8,3,0,5,1] :=
  branch_excluded a [4,7,6,8,3,0,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,3,0,5,1,0] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,1,1] (by decide +kernel))
      node_685
      (invalid_excluded a [4,7,6,8,3,0,5,1,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,1,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,1,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,1,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,1,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,1,8] (by decide +kernel)))

theorem node_686 : Excluded a [4,7,6,8,3,0,5,2] :=
  source_excluded a [4,7,6,8,3,0,5,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_683 : Excluded a [4,7,6,8,3,0,5] :=
  branch_excluded a [4,7,6,8,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,3,0,5,0] (by decide +kernel))
      node_684
      node_686
      (invalid_excluded a [4,7,6,8,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,8] (by decide +kernel)))

theorem node_680 : Excluded a [4,7,6,8,3,0] :=
  branch_excluded a [4,7,6,8,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,3,0,0] (by decide +kernel))
      node_681
      node_682
      (invalid_excluded a [4,7,6,8,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,4] (by decide +kernel))
      node_683
      (invalid_excluded a [4,7,6,8,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,8] (by decide +kernel)))

theorem node_687 : Excluded a [4,7,6,8,3,1] :=
  predecessor_excluded a [4,7,6,8,3,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_688 : Excluded a [4,7,6,8,3,2] :=
  source_excluded a [4,7,6,8,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_679 : Excluded a [4,7,6,8,3] :=
  branch_excluded a [4,7,6,8,3] (by decide)
    (fin9_cases _
      node_680
      node_687
      node_688
      (invalid_excluded a [4,7,6,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,8] (by decide +kernel)))

theorem node_675 : Excluded a [4,7,6,8] :=
  branch_excluded a [4,7,6,8] (by decide)
    (fin9_cases _
      node_676
      node_677
      node_678
      node_679
      (invalid_excluded a [4,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,8] (by decide +kernel)))

theorem node_657 : Excluded a [4,7,6] :=
  branch_excluded a [4,7,6] (by decide)
    (fin9_cases _
      node_658
      node_659
      node_660
      (invalid_excluded a [4,7,6,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,4] (by decide +kernel))
      node_674
      (invalid_excluded a [4,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,7] (by decide +kernel))
      node_675)

theorem node_689 : Excluded a [4,7,8] :=
  predecessor_excluded a [4,7,8] 0 8 1 2 (by decide) (by decide +kernel)

theorem node_598 : Excluded a [4,7] :=
  branch_excluded a [4,7] (by decide)
    (fin9_cases _
      node_599
      node_600
      (invalid_excluded a [4,7,2] (by decide +kernel))
      (invalid_excluded a [4,7,3] (by decide +kernel))
      (invalid_excluded a [4,7,4] (by decide +kernel))
      node_646
      node_657
      (invalid_excluded a [4,7,7] (by decide +kernel))
      node_689)

theorem node_691 : Excluded a [4,8,0] :=
  predecessor_excluded a [4,8,0] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_693 : Excluded a [4,8,1,0] :=
  source_excluded a [4,8,1,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_694 : Excluded a [4,8,1,2] :=
  predecessor_excluded a [4,8,1,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_695 : Excluded a [4,8,1,5] :=
  source_excluded a [4,8,1,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_699 : Excluded a [4,8,1,6,0,2,3] :=
  predecessor_excluded a [4,8,1,6,0,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_700 : Excluded a [4,8,1,6,0,2,5] :=
  predecessor_excluded a [4,8,1,6,0,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_698 : Excluded a [4,8,1,6,0,2] :=
  branch_excluded a [4,8,1,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,6,0,2,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,0,2,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,0,2,2] (by decide +kernel))
      node_699
      (invalid_excluded a [4,8,1,6,0,2,4] (by decide +kernel))
      node_700
      (invalid_excluded a [4,8,1,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,0,2,8] (by decide +kernel)))

theorem node_701 : Excluded a [4,8,1,6,0,3] :=
  source_excluded a [4,8,1,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_702 : Excluded a [4,8,1,6,0,7] :=
  source_excluded a [4,8,1,6,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_697 : Excluded a [4,8,1,6,0] :=
  branch_excluded a [4,8,1,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,6,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,0,1] (by decide +kernel))
      node_698
      node_701
      (invalid_excluded a [4,8,1,6,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,0,6] (by decide +kernel))
      node_702
      (invalid_excluded a [4,8,1,6,0,8] (by decide +kernel)))

theorem node_703 : Excluded a [4,8,1,6,2] :=
  predecessor_excluded a [4,8,1,6,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_704 : Excluded a [4,8,1,6,3] :=
  predecessor_excluded a [4,8,1,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_705 : Excluded a [4,8,1,6,7] :=
  predecessor_excluded a [4,8,1,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_696 : Excluded a [4,8,1,6] :=
  branch_excluded a [4,8,1,6] (by decide)
    (fin9_cases _
      node_697
      (invalid_excluded a [4,8,1,6,1] (by decide +kernel))
      node_703
      node_704
      (invalid_excluded a [4,8,1,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,6] (by decide +kernel))
      node_705
      (invalid_excluded a [4,8,1,6,8] (by decide +kernel)))

theorem node_709 : Excluded a [4,8,1,7,0,2,3] :=
  source_excluded a [4,8,1,7,0,2,3] 6 0 3 (by decide) (by decide +kernel)

def b_712 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 8
  | 2 => 1
  | 3 => 7
  | 4 => 0
  | 5 => 2
  | 6 => 5
  | 7 => 3
  | 8 => 6
  | _ => 0

def cert_712 : LosingRegion (edgeOf a b_712) 0 :=
  losingMask a b_712 0 1210110022419660917507072
    (by decide +kernel) (by decide +kernel)

theorem node_712 : Excluded a [4,8,1,7,0,2,5,3,6] :=
  losing_excluded a [4,8,1,7,0,2,5,3,6] (by decide) b_712 (by decide +kernel) 1 0 7 cert_712 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_712 1 0 ∧ 7 ≠ 1 ∧ maskRegion 1210110022419660917507072 1 7; decide +kernel)

theorem node_711 : Excluded a [4,8,1,7,0,2,5,3] :=
  branch_excluded a [4,8,1,7,0,2,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,0,2,5,3,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,2,5,3,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,2,5,3,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,2,5,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,2,5,3,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,2,5,3,5] (by decide +kernel))
      node_712
      (invalid_excluded a [4,8,1,7,0,2,5,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,2,5,3,8] (by decide +kernel)))

theorem node_713 : Excluded a [4,8,1,7,0,2,5,6] :=
  predecessor_excluded a [4,8,1,7,0,2,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_710 : Excluded a [4,8,1,7,0,2,5] :=
  branch_excluded a [4,8,1,7,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,0,2,5,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,2,5,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,2,5,2] (by decide +kernel))
      node_711
      (invalid_excluded a [4,8,1,7,0,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,2,5,5] (by decide +kernel))
      node_713
      (invalid_excluded a [4,8,1,7,0,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,2,5,8] (by decide +kernel)))

theorem node_708 : Excluded a [4,8,1,7,0,2] :=
  branch_excluded a [4,8,1,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,0,2,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,2,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,2,2] (by decide +kernel))
      node_709
      (invalid_excluded a [4,8,1,7,0,2,4] (by decide +kernel))
      node_710
      (invalid_excluded a [4,8,1,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,2,8] (by decide +kernel)))

theorem node_714 : Excluded a [4,8,1,7,0,3] :=
  predecessor_excluded a [4,8,1,7,0,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_707 : Excluded a [4,8,1,7,0] :=
  branch_excluded a [4,8,1,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,1] (by decide +kernel))
      node_708
      node_714
      (invalid_excluded a [4,8,1,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,0,8] (by decide +kernel)))

theorem node_715 : Excluded a [4,8,1,7,2] :=
  predecessor_excluded a [4,8,1,7,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_719 : Excluded a [4,8,1,7,3,0,2,5] :=
  predecessor_excluded a [4,8,1,7,3,0,2,5] 1 0 7 5 (by decide) (by decide +kernel)

theorem node_721 : Excluded a [4,8,1,7,3,0,2,6,5] :=
  source_excluded a [4,8,1,7,3,0,2,6,5] 8 1 5 (by decide) (by decide +kernel)

theorem node_720 : Excluded a [4,8,1,7,3,0,2,6] :=
  branch_excluded a [4,8,1,7,3,0,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,3,0,2,6,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,6,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,6,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,6,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,6,4] (by decide +kernel))
      node_721
      (invalid_excluded a [4,8,1,7,3,0,2,6,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,6,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,6,8] (by decide +kernel)))

theorem node_718 : Excluded a [4,8,1,7,3,0,2] :=
  branch_excluded a [4,8,1,7,3,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,3,0,2,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,4] (by decide +kernel))
      node_719
      node_720
      (invalid_excluded a [4,8,1,7,3,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,8] (by decide +kernel)))

theorem node_723 : Excluded a [4,8,1,7,3,0,5,2] :=
  source_excluded a [4,8,1,7,3,0,5,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_724 : Excluded a [4,8,1,7,3,0,5,6] :=
  predecessor_excluded a [4,8,1,7,3,0,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_722 : Excluded a [4,8,1,7,3,0,5] :=
  branch_excluded a [4,8,1,7,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,3,0,5,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,5,1] (by decide +kernel))
      node_723
      (invalid_excluded a [4,8,1,7,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,5,5] (by decide +kernel))
      node_724
      (invalid_excluded a [4,8,1,7,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,5,8] (by decide +kernel)))

theorem node_717 : Excluded a [4,8,1,7,3,0] :=
  branch_excluded a [4,8,1,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,3,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,1] (by decide +kernel))
      node_718
      (invalid_excluded a [4,8,1,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,4] (by decide +kernel))
      node_722
      (invalid_excluded a [4,8,1,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,8] (by decide +kernel)))

theorem node_727 : Excluded a [4,8,1,7,3,2,0,5] :=
  predecessor_excluded a [4,8,1,7,3,2,0,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_728 : Excluded a [4,8,1,7,3,2,0,6] :=
  predecessor_excluded a [4,8,1,7,3,2,0,6] 1 0 7 6 (by decide) (by decide +kernel)

theorem node_726 : Excluded a [4,8,1,7,3,2,0] :=
  branch_excluded a [4,8,1,7,3,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,3,2,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,4] (by decide +kernel))
      node_727
      node_728
      (invalid_excluded a [4,8,1,7,3,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,8] (by decide +kernel)))

theorem node_730 : Excluded a [4,8,1,7,3,2,5,0] :=
  source_excluded a [4,8,1,7,3,2,5,0] 7 1 8 (by decide) (by decide +kernel)

theorem node_731 : Excluded a [4,8,1,7,3,2,5,6] :=
  predecessor_excluded a [4,8,1,7,3,2,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_729 : Excluded a [4,8,1,7,3,2,5] :=
  branch_excluded a [4,8,1,7,3,2,5] (by decide)
    (fin9_cases _
      node_730
      (invalid_excluded a [4,8,1,7,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,5,5] (by decide +kernel))
      node_731
      (invalid_excluded a [4,8,1,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,5,8] (by decide +kernel)))

theorem node_725 : Excluded a [4,8,1,7,3,2] :=
  branch_excluded a [4,8,1,7,3,2] (by decide)
    (fin9_cases _
      node_726
      (invalid_excluded a [4,8,1,7,3,2,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,4] (by decide +kernel))
      node_729
      (invalid_excluded a [4,8,1,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,8] (by decide +kernel)))

theorem node_716 : Excluded a [4,8,1,7,3] :=
  branch_excluded a [4,8,1,7,3] (by decide)
    (fin9_cases _
      node_717
      (invalid_excluded a [4,8,1,7,3,1] (by decide +kernel))
      node_725
      (invalid_excluded a [4,8,1,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,8] (by decide +kernel)))

theorem node_732 : Excluded a [4,8,1,7,6] :=
  source_excluded a [4,8,1,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_706 : Excluded a [4,8,1,7] :=
  branch_excluded a [4,8,1,7] (by decide)
    (fin9_cases _
      node_707
      (invalid_excluded a [4,8,1,7,1] (by decide +kernel))
      node_715
      node_716
      (invalid_excluded a [4,8,1,7,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5] (by decide +kernel))
      node_732
      (invalid_excluded a [4,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,8] (by decide +kernel)))

theorem node_692 : Excluded a [4,8,1] :=
  branch_excluded a [4,8,1] (by decide)
    (fin9_cases _
      node_693
      (invalid_excluded a [4,8,1,1] (by decide +kernel))
      node_694
      (invalid_excluded a [4,8,1,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,4] (by decide +kernel))
      node_695
      node_696
      node_706
      (invalid_excluded a [4,8,1,8] (by decide +kernel)))

theorem node_734 : Excluded a [4,8,5,0] :=
  source_excluded a [4,8,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_735 : Excluded a [4,8,5,1] :=
  source_excluded a [4,8,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_736 : Excluded a [4,8,5,2] :=
  predecessor_excluded a [4,8,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_737 : Excluded a [4,8,5,6] :=
  predecessor_excluded a [4,8,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_740 : Excluded a [4,8,5,7,0,1] :=
  predecessor_excluded a [4,8,5,7,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_742 : Excluded a [4,8,5,7,0,2,1] :=
  predecessor_excluded a [4,8,5,7,0,2,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_743 : Excluded a [4,8,5,7,0,2,3] :=
  source_excluded a [4,8,5,7,0,2,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_741 : Excluded a [4,8,5,7,0,2] :=
  branch_excluded a [4,8,5,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,5,7,0,2,0] (by decide +kernel))
      node_742
      (invalid_excluded a [4,8,5,7,0,2,2] (by decide +kernel))
      node_743
      (invalid_excluded a [4,8,5,7,0,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,0,2,8] (by decide +kernel)))

theorem node_744 : Excluded a [4,8,5,7,0,3] :=
  source_excluded a [4,8,5,7,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_739 : Excluded a [4,8,5,7,0] :=
  branch_excluded a [4,8,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,5,7,0,0] (by decide +kernel))
      node_740
      node_741
      node_744
      (invalid_excluded a [4,8,5,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,0,8] (by decide +kernel)))

theorem node_745 : Excluded a [4,8,5,7,1] :=
  source_excluded a [4,8,5,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_746 : Excluded a [4,8,5,7,2] :=
  source_excluded a [4,8,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_747 : Excluded a [4,8,5,7,3] :=
  source_excluded a [4,8,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_748 : Excluded a [4,8,5,7,6] :=
  source_excluded a [4,8,5,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_738 : Excluded a [4,8,5,7] :=
  branch_excluded a [4,8,5,7] (by decide)
    (fin9_cases _
      node_739
      node_745
      node_746
      node_747
      (invalid_excluded a [4,8,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,5] (by decide +kernel))
      node_748
      (invalid_excluded a [4,8,5,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,8] (by decide +kernel)))

theorem node_733 : Excluded a [4,8,5] :=
  branch_excluded a [4,8,5] (by decide)
    (fin9_cases _
      node_734
      node_735
      node_736
      (invalid_excluded a [4,8,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,5] (by decide +kernel))
      node_737
      node_738
      (invalid_excluded a [4,8,5,8] (by decide +kernel)))

theorem node_750 : Excluded a [4,8,6,0] :=
  source_excluded a [4,8,6,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_751 : Excluded a [4,8,6,1] :=
  source_excluded a [4,8,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_754 : Excluded a [4,8,6,2,0,1] :=
  predecessor_excluded a [4,8,6,2,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_755 : Excluded a [4,8,6,2,0,3] :=
  source_excluded a [4,8,6,2,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_756 : Excluded a [4,8,6,2,0,7] :=
  source_excluded a [4,8,6,2,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_753 : Excluded a [4,8,6,2,0] :=
  branch_excluded a [4,8,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,6,2,0,0] (by decide +kernel))
      node_754
      (invalid_excluded a [4,8,6,2,0,2] (by decide +kernel))
      node_755
      (invalid_excluded a [4,8,6,2,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,0,6] (by decide +kernel))
      node_756
      (invalid_excluded a [4,8,6,2,0,8] (by decide +kernel)))

theorem node_757 : Excluded a [4,8,6,2,1] :=
  source_excluded a [4,8,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_758 : Excluded a [4,8,6,2,3] :=
  predecessor_excluded a [4,8,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_761 : Excluded a [4,8,6,2,7,0,1] :=
  predecessor_excluded a [4,8,6,2,7,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_762 : Excluded a [4,8,6,2,7,0,3] :=
  source_excluded a [4,8,6,2,7,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_763 : Excluded a [4,8,6,2,7,0,5] :=
  source_excluded a [4,8,6,2,7,0,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_760 : Excluded a [4,8,6,2,7,0] :=
  branch_excluded a [4,8,6,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,6,2,7,0,0] (by decide +kernel))
      node_761
      (invalid_excluded a [4,8,6,2,7,0,2] (by decide +kernel))
      node_762
      (invalid_excluded a [4,8,6,2,7,0,4] (by decide +kernel))
      node_763
      (invalid_excluded a [4,8,6,2,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,0,8] (by decide +kernel)))

theorem node_767 : Excluded a [4,8,6,2,7,1,0,3,5] :=
  predecessor_excluded a [4,8,6,2,7,1,0,3,5] 2 1 8 5 (by decide) (by decide +kernel)

theorem node_766 : Excluded a [4,8,6,2,7,1,0,3] :=
  branch_excluded a [4,8,6,2,7,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,6,2,7,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,0,3,1] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,0,3,2] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,0,3,4] (by decide +kernel))
      node_767
      (invalid_excluded a [4,8,6,2,7,1,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,0,3,8] (by decide +kernel)))

theorem node_768 : Excluded a [4,8,6,2,7,1,0,5] :=
  source_excluded a [4,8,6,2,7,1,0,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_765 : Excluded a [4,8,6,2,7,1,0] :=
  branch_excluded a [4,8,6,2,7,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,6,2,7,1,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,0,1] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,0,2] (by decide +kernel))
      node_766
      (invalid_excluded a [4,8,6,2,7,1,0,4] (by decide +kernel))
      node_768
      (invalid_excluded a [4,8,6,2,7,1,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,0,8] (by decide +kernel)))

theorem node_769 : Excluded a [4,8,6,2,7,1,3] :=
  source_excluded a [4,8,6,2,7,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_770 : Excluded a [4,8,6,2,7,1,5] :=
  source_excluded a [4,8,6,2,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_764 : Excluded a [4,8,6,2,7,1] :=
  branch_excluded a [4,8,6,2,7,1] (by decide)
    (fin9_cases _
      node_765
      (invalid_excluded a [4,8,6,2,7,1,1] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,2] (by decide +kernel))
      node_769
      (invalid_excluded a [4,8,6,2,7,1,4] (by decide +kernel))
      node_770
      (invalid_excluded a [4,8,6,2,7,1,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,8] (by decide +kernel)))

theorem node_771 : Excluded a [4,8,6,2,7,3] :=
  source_excluded a [4,8,6,2,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_759 : Excluded a [4,8,6,2,7] :=
  branch_excluded a [4,8,6,2,7] (by decide)
    (fin9_cases _
      node_760
      node_764
      (invalid_excluded a [4,8,6,2,7,2] (by decide +kernel))
      node_771
      (invalid_excluded a [4,8,6,2,7,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,8] (by decide +kernel)))

theorem node_752 : Excluded a [4,8,6,2] :=
  branch_excluded a [4,8,6,2] (by decide)
    (fin9_cases _
      node_753
      node_757
      (invalid_excluded a [4,8,6,2,2] (by decide +kernel))
      node_758
      (invalid_excluded a [4,8,6,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,6] (by decide +kernel))
      node_759
      (invalid_excluded a [4,8,6,2,8] (by decide +kernel)))

theorem node_772 : Excluded a [4,8,6,5] :=
  source_excluded a [4,8,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_773 : Excluded a [4,8,6,7] :=
  predecessor_excluded a [4,8,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_749 : Excluded a [4,8,6] :=
  branch_excluded a [4,8,6] (by decide)
    (fin9_cases _
      node_750
      node_751
      node_752
      (invalid_excluded a [4,8,6,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,4] (by decide +kernel))
      node_772
      (invalid_excluded a [4,8,6,6] (by decide +kernel))
      node_773
      (invalid_excluded a [4,8,6,8] (by decide +kernel)))

theorem node_775 : Excluded a [4,8,7,0] :=
  source_excluded a [4,8,7,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_776 : Excluded a [4,8,7,1] :=
  source_excluded a [4,8,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_779 : Excluded a [4,8,7,2,0,1] :=
  predecessor_excluded a [4,8,7,2,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_781 : Excluded a [4,8,7,2,0,3,1] :=
  predecessor_excluded a [4,8,7,2,0,3,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_783 : Excluded a [4,8,7,2,0,3,5,1] :=
  source_excluded a [4,8,7,2,0,3,5,1] 7 0 1 (by decide) (by decide +kernel)

theorem node_784 : Excluded a [4,8,7,2,0,3,5,6] :=
  predecessor_excluded a [4,8,7,2,0,3,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_782 : Excluded a [4,8,7,2,0,3,5] :=
  branch_excluded a [4,8,7,2,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,7,2,0,3,5,0] (by decide +kernel))
      node_783
      (invalid_excluded a [4,8,7,2,0,3,5,2] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,0,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,0,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,0,3,5,5] (by decide +kernel))
      node_784
      (invalid_excluded a [4,8,7,2,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,0,3,5,8] (by decide +kernel)))

theorem node_780 : Excluded a [4,8,7,2,0,3] :=
  branch_excluded a [4,8,7,2,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,7,2,0,3,0] (by decide +kernel))
      node_781
      (invalid_excluded a [4,8,7,2,0,3,2] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,0,3,4] (by decide +kernel))
      node_782
      (invalid_excluded a [4,8,7,2,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,0,3,8] (by decide +kernel)))

theorem node_778 : Excluded a [4,8,7,2,0] :=
  branch_excluded a [4,8,7,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,7,2,0,0] (by decide +kernel))
      node_779
      (invalid_excluded a [4,8,7,2,0,2] (by decide +kernel))
      node_780
      (invalid_excluded a [4,8,7,2,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,0,8] (by decide +kernel)))

theorem node_785 : Excluded a [4,8,7,2,1] :=
  source_excluded a [4,8,7,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_786 : Excluded a [4,8,7,2,3] :=
  predecessor_excluded a [4,8,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_787 : Excluded a [4,8,7,2,6] :=
  source_excluded a [4,8,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_777 : Excluded a [4,8,7,2] :=
  branch_excluded a [4,8,7,2] (by decide)
    (fin9_cases _
      node_778
      node_785
      (invalid_excluded a [4,8,7,2,2] (by decide +kernel))
      node_786
      (invalid_excluded a [4,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,5] (by decide +kernel))
      node_787
      (invalid_excluded a [4,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,8] (by decide +kernel)))

theorem node_788 : Excluded a [4,8,7,5] :=
  source_excluded a [4,8,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_791 : Excluded a [4,8,7,6,0,1] :=
  predecessor_excluded a [4,8,7,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_792 : Excluded a [4,8,7,6,0,2] :=
  predecessor_excluded a [4,8,7,6,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_793 : Excluded a [4,8,7,6,0,3] :=
  source_excluded a [4,8,7,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_790 : Excluded a [4,8,7,6,0] :=
  branch_excluded a [4,8,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,7,6,0,0] (by decide +kernel))
      node_791
      node_792
      node_793
      (invalid_excluded a [4,8,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,0,8] (by decide +kernel)))

theorem node_794 : Excluded a [4,8,7,6,1] :=
  source_excluded a [4,8,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_795 : Excluded a [4,8,7,6,2] :=
  predecessor_excluded a [4,8,7,6,2] 3 2 0 4 (by decide) (by decide +kernel)

theorem node_796 : Excluded a [4,8,7,6,3] :=
  predecessor_excluded a [4,8,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_789 : Excluded a [4,8,7,6] :=
  branch_excluded a [4,8,7,6] (by decide)
    (fin9_cases _
      node_790
      node_794
      node_795
      node_796
      (invalid_excluded a [4,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,8] (by decide +kernel)))

theorem node_774 : Excluded a [4,8,7] :=
  branch_excluded a [4,8,7] (by decide)
    (fin9_cases _
      node_775
      node_776
      node_777
      (invalid_excluded a [4,8,7,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,4] (by decide +kernel))
      node_788
      node_789
      (invalid_excluded a [4,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,8] (by decide +kernel)))

theorem node_690 : Excluded a [4,8] :=
  branch_excluded a [4,8] (by decide)
    (fin9_cases _
      node_691
      node_692
      (invalid_excluded a [4,8,2] (by decide +kernel))
      (invalid_excluded a [4,8,3] (by decide +kernel))
      (invalid_excluded a [4,8,4] (by decide +kernel))
      node_733
      node_749
      node_774
      (invalid_excluded a [4,8,8] (by decide +kernel)))

theorem node_321 : Excluded a [4] :=
  branch_excluded a [4] (by decide)
    (fin9_cases _
      node_322
      (invalid_excluded a [4,1] (by decide +kernel))
      (invalid_excluded a [4,2] (by decide +kernel))
      node_463
      (invalid_excluded a [4,4] (by decide +kernel))
      node_464
      node_465
      node_598
      node_690)

theorem node_799 : Excluded a [5,0,1] :=
  predecessor_excluded a [5,0,1] 3 1 1 2 (by decide) (by decide +kernel)

theorem node_800 : Excluded a [5,0,4] :=
  source_excluded a [5,0,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_803 : Excluded a [5,0,6,1,2] :=
  predecessor_excluded a [5,0,6,1,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_805 : Excluded a [5,0,6,1,3,2] :=
  source_excluded a [5,0,6,1,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_806 : Excluded a [5,0,6,1,3,4] :=
  predecessor_excluded a [5,0,6,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_807 : Excluded a [5,0,6,1,3,7] :=
  source_excluded a [5,0,6,1,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_811 : Excluded a [5,0,6,1,3,8,2,4,7] :=
  predecessor_excluded a [5,0,6,1,3,8,2,4,7] 0 7 5 8 (by decide) (by decide +kernel)

theorem node_810 : Excluded a [5,0,6,1,3,8,2,4] :=
  branch_excluded a [5,0,6,1,3,8,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,1,3,8,2,4,0] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,2,4,1] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,2,4,2] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,2,4,3] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,2,4,6] (by decide +kernel))
      node_811
      (invalid_excluded a [5,0,6,1,3,8,2,4,8] (by decide +kernel)))

theorem node_809 : Excluded a [5,0,6,1,3,8,2] :=
  branch_excluded a [5,0,6,1,3,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,1,3,8,2,0] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,2,1] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,2,2] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,2,3] (by decide +kernel))
      node_810
      (invalid_excluded a [5,0,6,1,3,8,2,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,2,6] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,2,7] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,2,8] (by decide +kernel)))

theorem node_812 : Excluded a [5,0,6,1,3,8,4] :=
  predecessor_excluded a [5,0,6,1,3,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_808 : Excluded a [5,0,6,1,3,8] :=
  branch_excluded a [5,0,6,1,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,1,3,8,0] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,1] (by decide +kernel))
      node_809
      (invalid_excluded a [5,0,6,1,3,8,3] (by decide +kernel))
      node_812
      (invalid_excluded a [5,0,6,1,3,8,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,8,8] (by decide +kernel)))

theorem node_804 : Excluded a [5,0,6,1,3] :=
  branch_excluded a [5,0,6,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,1,3,0] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,1] (by decide +kernel))
      node_805
      (invalid_excluded a [5,0,6,1,3,3] (by decide +kernel))
      node_806
      (invalid_excluded a [5,0,6,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,3,6] (by decide +kernel))
      node_807
      node_808)

theorem node_814 : Excluded a [5,0,6,1,7,2] :=
  source_excluded a [5,0,6,1,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_815 : Excluded a [5,0,6,1,7,3] :=
  source_excluded a [5,0,6,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_816 : Excluded a [5,0,6,1,7,4] :=
  predecessor_excluded a [5,0,6,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_817 : Excluded a [5,0,6,1,7,8] :=
  predecessor_excluded a [5,0,6,1,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_813 : Excluded a [5,0,6,1,7] :=
  branch_excluded a [5,0,6,1,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,1,7,0] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,7,1] (by decide +kernel))
      node_814
      node_815
      node_816
      (invalid_excluded a [5,0,6,1,7,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,7,7] (by decide +kernel))
      node_817)

theorem node_819 : Excluded a [5,0,6,1,8,2] :=
  source_excluded a [5,0,6,1,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_820 : Excluded a [5,0,6,1,8,3] :=
  source_excluded a [5,0,6,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_823 : Excluded a [5,0,6,1,8,4,2,3] :=
  predecessor_excluded a [5,0,6,1,8,4,2,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_822 : Excluded a [5,0,6,1,8,4,2] :=
  branch_excluded a [5,0,6,1,8,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,1,8,4,2,0] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,8,4,2,1] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,8,4,2,2] (by decide +kernel))
      node_823
      (invalid_excluded a [5,0,6,1,8,4,2,4] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,8,4,2,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,8,4,2,6] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,8,4,2,7] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,8,4,2,8] (by decide +kernel)))

theorem node_824 : Excluded a [5,0,6,1,8,4,3] :=
  source_excluded a [5,0,6,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_821 : Excluded a [5,0,6,1,8,4] :=
  branch_excluded a [5,0,6,1,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,1,8,4,0] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,8,4,1] (by decide +kernel))
      node_822
      node_824
      (invalid_excluded a [5,0,6,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,8,4,8] (by decide +kernel)))

theorem node_825 : Excluded a [5,0,6,1,8,7] :=
  source_excluded a [5,0,6,1,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_818 : Excluded a [5,0,6,1,8] :=
  branch_excluded a [5,0,6,1,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,1,8,0] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,8,1] (by decide +kernel))
      node_819
      node_820
      node_821
      (invalid_excluded a [5,0,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,8,6] (by decide +kernel))
      node_825
      (invalid_excluded a [5,0,6,1,8,8] (by decide +kernel)))

theorem node_802 : Excluded a [5,0,6,1] :=
  branch_excluded a [5,0,6,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,1,0] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,1] (by decide +kernel))
      node_803
      node_804
      (invalid_excluded a [5,0,6,1,4] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,1,6] (by decide +kernel))
      node_813
      node_818)

theorem node_827 : Excluded a [5,0,6,2,1] :=
  source_excluded a [5,0,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_828 : Excluded a [5,0,6,2,3] :=
  predecessor_excluded a [5,0,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_830 : Excluded a [5,0,6,2,7,1] :=
  source_excluded a [5,0,6,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_831 : Excluded a [5,0,6,2,7,3] :=
  source_excluded a [5,0,6,2,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_832 : Excluded a [5,0,6,2,7,4] :=
  predecessor_excluded a [5,0,6,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_833 : Excluded a [5,0,6,2,7,8] :=
  predecessor_excluded a [5,0,6,2,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_829 : Excluded a [5,0,6,2,7] :=
  branch_excluded a [5,0,6,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,2,7,0] (by decide +kernel))
      node_830
      (invalid_excluded a [5,0,6,2,7,2] (by decide +kernel))
      node_831
      node_832
      (invalid_excluded a [5,0,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,7,7] (by decide +kernel))
      node_833)

theorem node_835 : Excluded a [5,0,6,2,8,1] :=
  source_excluded a [5,0,6,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_836 : Excluded a [5,0,6,2,8,3] :=
  source_excluded a [5,0,6,2,8,3] 2 0 5 (by decide) (by decide +kernel)

def b_840 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 0
  | 2 => 6
  | 3 => 2
  | 4 => 8
  | 5 => 4
  | 6 => 1
  | 7 => 3
  | 8 => 7
  | _ => 0

def cert_840 : LosingRegion (edgeOf a b_840) 0 :=
  losingMask a b_840 0 1210255139236447813370880
    (by decide +kernel) (by decide +kernel)

theorem node_840 : Excluded a [5,0,6,2,8,4,1,3,7] :=
  losing_excluded a [5,0,6,2,8,4,1,3,7] (by decide) b_840 (by decide +kernel) 2 0 5 cert_840 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_840 2 0 ∧ 5 ≠ 2 ∧ maskRegion 1210255139236447813370880 2 5; decide +kernel)

theorem node_839 : Excluded a [5,0,6,2,8,4,1,3] :=
  branch_excluded a [5,0,6,2,8,4,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,2,8,4,1,3,0] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,1,3,1] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,1,3,2] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,1,3,3] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,1,3,4] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,1,3,6] (by decide +kernel))
      node_840
      (invalid_excluded a [5,0,6,2,8,4,1,3,8] (by decide +kernel)))

theorem node_838 : Excluded a [5,0,6,2,8,4,1] :=
  branch_excluded a [5,0,6,2,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,2,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,1,2] (by decide +kernel))
      node_839
      (invalid_excluded a [5,0,6,2,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,1,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,1,6] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,1,8] (by decide +kernel)))

theorem node_841 : Excluded a [5,0,6,2,8,4,3] :=
  source_excluded a [5,0,6,2,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_837 : Excluded a [5,0,6,2,8,4] :=
  branch_excluded a [5,0,6,2,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,2,8,4,0] (by decide +kernel))
      node_838
      (invalid_excluded a [5,0,6,2,8,4,2] (by decide +kernel))
      node_841
      (invalid_excluded a [5,0,6,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,4,8] (by decide +kernel)))

theorem node_842 : Excluded a [5,0,6,2,8,7] :=
  source_excluded a [5,0,6,2,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_834 : Excluded a [5,0,6,2,8] :=
  branch_excluded a [5,0,6,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,2,8,0] (by decide +kernel))
      node_835
      (invalid_excluded a [5,0,6,2,8,2] (by decide +kernel))
      node_836
      node_837
      (invalid_excluded a [5,0,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,8,6] (by decide +kernel))
      node_842
      (invalid_excluded a [5,0,6,2,8,8] (by decide +kernel)))

theorem node_826 : Excluded a [5,0,6,2] :=
  branch_excluded a [5,0,6,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,2,0] (by decide +kernel))
      node_827
      (invalid_excluded a [5,0,6,2,2] (by decide +kernel))
      node_828
      (invalid_excluded a [5,0,6,2,4] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,2,6] (by decide +kernel))
      node_829
      node_834)

theorem node_843 : Excluded a [5,0,6,7] :=
  predecessor_excluded a [5,0,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_845 : Excluded a [5,0,6,8,1] :=
  source_excluded a [5,0,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_846 : Excluded a [5,0,6,8,2] :=
  predecessor_excluded a [5,0,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_848 : Excluded a [5,0,6,8,3,1] :=
  source_excluded a [5,0,6,8,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_849 : Excluded a [5,0,6,8,3,2] :=
  source_excluded a [5,0,6,8,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_850 : Excluded a [5,0,6,8,3,4] :=
  predecessor_excluded a [5,0,6,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_851 : Excluded a [5,0,6,8,3,7] :=
  source_excluded a [5,0,6,8,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_847 : Excluded a [5,0,6,8,3] :=
  branch_excluded a [5,0,6,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,8,3,0] (by decide +kernel))
      node_848
      node_849
      (invalid_excluded a [5,0,6,8,3,3] (by decide +kernel))
      node_850
      (invalid_excluded a [5,0,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,8,3,6] (by decide +kernel))
      node_851
      (invalid_excluded a [5,0,6,8,3,8] (by decide +kernel)))

theorem node_853 : Excluded a [5,0,6,8,7,1] :=
  source_excluded a [5,0,6,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_854 : Excluded a [5,0,6,8,7,2] :=
  source_excluded a [5,0,6,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_855 : Excluded a [5,0,6,8,7,3] :=
  source_excluded a [5,0,6,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_856 : Excluded a [5,0,6,8,7,4] :=
  predecessor_excluded a [5,0,6,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_852 : Excluded a [5,0,6,8,7] :=
  branch_excluded a [5,0,6,8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,8,7,0] (by decide +kernel))
      node_853
      node_854
      node_855
      node_856
      (invalid_excluded a [5,0,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,0,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,0,6,8,7,8] (by decide +kernel)))

theorem node_844 : Excluded a [5,0,6,8] :=
  branch_excluded a [5,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,8,0] (by decide +kernel))
      node_845
      node_846
      node_847
      (invalid_excluded a [5,0,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,8,6] (by decide +kernel))
      node_852
      (invalid_excluded a [5,0,6,8,8] (by decide +kernel)))

theorem node_801 : Excluded a [5,0,6] :=
  branch_excluded a [5,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,6,0] (by decide +kernel))
      node_802
      node_826
      (invalid_excluded a [5,0,6,3] (by decide +kernel))
      (invalid_excluded a [5,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,0,6,6] (by decide +kernel))
      node_843
      node_844)

theorem node_859 : Excluded a [5,0,7,1,2] :=
  predecessor_excluded a [5,0,7,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_861 : Excluded a [5,0,7,1,3,2] :=
  predecessor_excluded a [5,0,7,1,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_862 : Excluded a [5,0,7,1,3,4] :=
  predecessor_excluded a [5,0,7,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_864 : Excluded a [5,0,7,1,3,8,2] :=
  source_excluded a [5,0,7,1,3,8,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_867 : Excluded a [5,0,7,1,3,8,4,2,6] :=
  source_excluded a [5,0,7,1,3,8,4,2,6] 5 0 8 (by decide) (by decide +kernel)

theorem node_866 : Excluded a [5,0,7,1,3,8,4,2] :=
  branch_excluded a [5,0,7,1,3,8,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,1,3,8,4,2,0] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,8,4,2,1] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,8,4,2,2] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,8,4,2,3] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,8,4,2,4] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,8,4,2,5] (by decide +kernel))
      node_867
      (invalid_excluded a [5,0,7,1,3,8,4,2,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,8,4,2,8] (by decide +kernel)))

theorem node_868 : Excluded a [5,0,7,1,3,8,4,6] :=
  source_excluded a [5,0,7,1,3,8,4,6] 5 0 7 (by decide) (by decide +kernel)

theorem node_865 : Excluded a [5,0,7,1,3,8,4] :=
  branch_excluded a [5,0,7,1,3,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,1,3,8,4,0] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,8,4,1] (by decide +kernel))
      node_866
      (invalid_excluded a [5,0,7,1,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,8,4,5] (by decide +kernel))
      node_868
      (invalid_excluded a [5,0,7,1,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,8,4,8] (by decide +kernel)))

theorem node_863 : Excluded a [5,0,7,1,3,8] :=
  branch_excluded a [5,0,7,1,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,1,3,8,0] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,8,1] (by decide +kernel))
      node_864
      (invalid_excluded a [5,0,7,1,3,8,3] (by decide +kernel))
      node_865
      (invalid_excluded a [5,0,7,1,3,8,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,8,8] (by decide +kernel)))

theorem node_860 : Excluded a [5,0,7,1,3] :=
  branch_excluded a [5,0,7,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,1,3,0] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,1] (by decide +kernel))
      node_861
      (invalid_excluded a [5,0,7,1,3,3] (by decide +kernel))
      node_862
      (invalid_excluded a [5,0,7,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,3,7] (by decide +kernel))
      node_863)

theorem node_869 : Excluded a [5,0,7,1,6] :=
  source_excluded a [5,0,7,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_871 : Excluded a [5,0,7,1,8,2] :=
  predecessor_excluded a [5,0,7,1,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_873 : Excluded a [5,0,7,1,8,3,2] :=
  source_excluded a [5,0,7,1,8,3,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_874 : Excluded a [5,0,7,1,8,3,4] :=
  predecessor_excluded a [5,0,7,1,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_872 : Excluded a [5,0,7,1,8,3] :=
  branch_excluded a [5,0,7,1,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,1,8,3,0] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,8,3,1] (by decide +kernel))
      node_873
      (invalid_excluded a [5,0,7,1,8,3,3] (by decide +kernel))
      node_874
      (invalid_excluded a [5,0,7,1,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,8,3,8] (by decide +kernel)))

theorem node_876 : Excluded a [5,0,7,1,8,4,2] :=
  source_excluded a [5,0,7,1,8,4,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_877 : Excluded a [5,0,7,1,8,4,3] :=
  source_excluded a [5,0,7,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_875 : Excluded a [5,0,7,1,8,4] :=
  branch_excluded a [5,0,7,1,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,1,8,4,0] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,8,4,1] (by decide +kernel))
      node_876
      node_877
      (invalid_excluded a [5,0,7,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,8,4,8] (by decide +kernel)))

theorem node_870 : Excluded a [5,0,7,1,8] :=
  branch_excluded a [5,0,7,1,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,1,8,0] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,8,1] (by decide +kernel))
      node_871
      node_872
      node_875
      (invalid_excluded a [5,0,7,1,8,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,8,8] (by decide +kernel)))

theorem node_858 : Excluded a [5,0,7,1] :=
  branch_excluded a [5,0,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,1,0] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,1] (by decide +kernel))
      node_859
      node_860
      (invalid_excluded a [5,0,7,1,4] (by decide +kernel))
      (invalid_excluded a [5,0,7,1,5] (by decide +kernel))
      node_869
      (invalid_excluded a [5,0,7,1,7] (by decide +kernel))
      node_870)

theorem node_879 : Excluded a [5,0,7,2,1] :=
  source_excluded a [5,0,7,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_880 : Excluded a [5,0,7,2,3] :=
  predecessor_excluded a [5,0,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_881 : Excluded a [5,0,7,2,6] :=
  source_excluded a [5,0,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_883 : Excluded a [5,0,7,2,8,1] :=
  source_excluded a [5,0,7,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_886 : Excluded a [5,0,7,2,8,3,1,4] :=
  source_excluded a [5,0,7,2,8,3,1,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_888 : Excluded a [5,0,7,2,8,3,1,6,4] :=
  predecessor_excluded a [5,0,7,2,8,3,1,6,4] 1 5 8 0 (by decide) (by decide +kernel)

theorem node_887 : Excluded a [5,0,7,2,8,3,1,6] :=
  branch_excluded a [5,0,7,2,8,3,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,2,8,3,1,6,0] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,3,1,6,1] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,3,1,6,2] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,3,1,6,3] (by decide +kernel))
      node_888
      (invalid_excluded a [5,0,7,2,8,3,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,3,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,3,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,3,1,6,8] (by decide +kernel)))

theorem node_885 : Excluded a [5,0,7,2,8,3,1] :=
  branch_excluded a [5,0,7,2,8,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,2,8,3,1,0] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,3,1,1] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,3,1,2] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,3,1,3] (by decide +kernel))
      node_886
      (invalid_excluded a [5,0,7,2,8,3,1,5] (by decide +kernel))
      node_887
      (invalid_excluded a [5,0,7,2,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,3,1,8] (by decide +kernel)))

theorem node_889 : Excluded a [5,0,7,2,8,3,4] :=
  predecessor_excluded a [5,0,7,2,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_884 : Excluded a [5,0,7,2,8,3] :=
  branch_excluded a [5,0,7,2,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,2,8,3,0] (by decide +kernel))
      node_885
      (invalid_excluded a [5,0,7,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,3,3] (by decide +kernel))
      node_889
      (invalid_excluded a [5,0,7,2,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,3,8] (by decide +kernel)))

theorem node_892 : Excluded a [5,0,7,2,8,4,1,3] :=
  source_excluded a [5,0,7,2,8,4,1,3] 2 0 7 (by decide) (by decide +kernel)

def b_894 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 0
  | 2 => 7
  | 3 => 2
  | 4 => 8
  | 5 => 4
  | 6 => 1
  | 7 => 6
  | 8 => 3
  | _ => 0

def cert_894 : LosingRegion (edgeOf a b_894) 0 :=
  losingMask a b_894 0 1210107572048077872169984
    (by decide +kernel) (by decide +kernel)

theorem node_894 : Excluded a [5,0,7,2,8,4,1,6,3] :=
  losing_excluded a [5,0,7,2,8,4,1,6,3] (by decide) b_894 (by decide +kernel) 2 0 6 cert_894 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_894 2 0 ∧ 6 ≠ 2 ∧ maskRegion 1210107572048077872169984 2 6; decide +kernel)

theorem node_893 : Excluded a [5,0,7,2,8,4,1,6] :=
  branch_excluded a [5,0,7,2,8,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,2,8,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,4,1,6,2] (by decide +kernel))
      node_894
      (invalid_excluded a [5,0,7,2,8,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,4,1,6,8] (by decide +kernel)))

theorem node_891 : Excluded a [5,0,7,2,8,4,1] :=
  branch_excluded a [5,0,7,2,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,2,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,4,1,2] (by decide +kernel))
      node_892
      (invalid_excluded a [5,0,7,2,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,4,1,5] (by decide +kernel))
      node_893
      (invalid_excluded a [5,0,7,2,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,4,1,8] (by decide +kernel)))

theorem node_895 : Excluded a [5,0,7,2,8,4,3] :=
  source_excluded a [5,0,7,2,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_890 : Excluded a [5,0,7,2,8,4] :=
  branch_excluded a [5,0,7,2,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,2,8,4,0] (by decide +kernel))
      node_891
      (invalid_excluded a [5,0,7,2,8,4,2] (by decide +kernel))
      node_895
      (invalid_excluded a [5,0,7,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,4,8] (by decide +kernel)))

theorem node_882 : Excluded a [5,0,7,2,8] :=
  branch_excluded a [5,0,7,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,2,8,0] (by decide +kernel))
      node_883
      (invalid_excluded a [5,0,7,2,8,2] (by decide +kernel))
      node_884
      node_890
      (invalid_excluded a [5,0,7,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,8,8] (by decide +kernel)))

theorem node_878 : Excluded a [5,0,7,2] :=
  branch_excluded a [5,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,2,0] (by decide +kernel))
      node_879
      (invalid_excluded a [5,0,7,2,2] (by decide +kernel))
      node_880
      (invalid_excluded a [5,0,7,2,4] (by decide +kernel))
      (invalid_excluded a [5,0,7,2,5] (by decide +kernel))
      node_881
      (invalid_excluded a [5,0,7,2,7] (by decide +kernel))
      node_882)

theorem node_897 : Excluded a [5,0,7,6,1] :=
  source_excluded a [5,0,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_899 : Excluded a [5,0,7,6,2,1] :=
  source_excluded a [5,0,7,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_900 : Excluded a [5,0,7,6,2,3] :=
  source_excluded a [5,0,7,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_901 : Excluded a [5,0,7,6,2,4] :=
  source_excluded a [5,0,7,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_904 : Excluded a [5,0,7,6,2,8,1,3] :=
  source_excluded a [5,0,7,6,2,8,1,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_905 : Excluded a [5,0,7,6,2,8,1,4] :=
  predecessor_excluded a [5,0,7,6,2,8,1,4] 0 4 2 7 (by decide) (by decide +kernel)

theorem node_903 : Excluded a [5,0,7,6,2,8,1] :=
  branch_excluded a [5,0,7,6,2,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,6,2,8,1,0] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,2,8,1,2] (by decide +kernel))
      node_904
      node_905
      (invalid_excluded a [5,0,7,6,2,8,1,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,2,8,1,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,2,8,1,8] (by decide +kernel)))

theorem node_906 : Excluded a [5,0,7,6,2,8,3] :=
  source_excluded a [5,0,7,6,2,8,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_907 : Excluded a [5,0,7,6,2,8,4] :=
  source_excluded a [5,0,7,6,2,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_902 : Excluded a [5,0,7,6,2,8] :=
  branch_excluded a [5,0,7,6,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,6,2,8,0] (by decide +kernel))
      node_903
      (invalid_excluded a [5,0,7,6,2,8,2] (by decide +kernel))
      node_906
      node_907
      (invalid_excluded a [5,0,7,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,2,8,8] (by decide +kernel)))

theorem node_898 : Excluded a [5,0,7,6,2] :=
  branch_excluded a [5,0,7,6,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,6,2,0] (by decide +kernel))
      node_899
      (invalid_excluded a [5,0,7,6,2,2] (by decide +kernel))
      node_900
      node_901
      (invalid_excluded a [5,0,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,2,7] (by decide +kernel))
      node_902)

theorem node_908 : Excluded a [5,0,7,6,3] :=
  predecessor_excluded a [5,0,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_910 : Excluded a [5,0,7,6,8,1] :=
  source_excluded a [5,0,7,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_911 : Excluded a [5,0,7,6,8,2] :=
  predecessor_excluded a [5,0,7,6,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_912 : Excluded a [5,0,7,6,8,3] :=
  source_excluded a [5,0,7,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_913 : Excluded a [5,0,7,6,8,4] :=
  source_excluded a [5,0,7,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_909 : Excluded a [5,0,7,6,8] :=
  branch_excluded a [5,0,7,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,6,8,0] (by decide +kernel))
      node_910
      node_911
      node_912
      node_913
      (invalid_excluded a [5,0,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,8,8] (by decide +kernel)))

theorem node_896 : Excluded a [5,0,7,6] :=
  branch_excluded a [5,0,7,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,6,0] (by decide +kernel))
      node_897
      node_898
      node_908
      (invalid_excluded a [5,0,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,0,7,6,7] (by decide +kernel))
      node_909)

theorem node_914 : Excluded a [5,0,7,8] :=
  predecessor_excluded a [5,0,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_857 : Excluded a [5,0,7] :=
  branch_excluded a [5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,7,0] (by decide +kernel))
      node_858
      node_878
      (invalid_excluded a [5,0,7,3] (by decide +kernel))
      (invalid_excluded a [5,0,7,4] (by decide +kernel))
      (invalid_excluded a [5,0,7,5] (by decide +kernel))
      node_896
      (invalid_excluded a [5,0,7,7] (by decide +kernel))
      node_914)

theorem node_917 : Excluded a [5,0,8,1,2] :=
  predecessor_excluded a [5,0,8,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_919 : Excluded a [5,0,8,1,3,2] :=
  predecessor_excluded a [5,0,8,1,3,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_920 : Excluded a [5,0,8,1,3,4] :=
  predecessor_excluded a [5,0,8,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_921 : Excluded a [5,0,8,1,3,7] :=
  source_excluded a [5,0,8,1,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_918 : Excluded a [5,0,8,1,3] :=
  branch_excluded a [5,0,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [5,0,8,1,3,1] (by decide +kernel))
      node_919
      (invalid_excluded a [5,0,8,1,3,3] (by decide +kernel))
      node_920
      (invalid_excluded a [5,0,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,0,8,1,3,6] (by decide +kernel))
      node_921
      (invalid_excluded a [5,0,8,1,3,8] (by decide +kernel)))

theorem node_922 : Excluded a [5,0,8,1,6] :=
  source_excluded a [5,0,8,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_924 : Excluded a [5,0,8,1,7,2] :=
  predecessor_excluded a [5,0,8,1,7,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_926 : Excluded a [5,0,8,1,7,3,2] :=
  predecessor_excluded a [5,0,8,1,7,3,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_927 : Excluded a [5,0,8,1,7,3,4] :=
  source_excluded a [5,0,8,1,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_925 : Excluded a [5,0,8,1,7,3] :=
  branch_excluded a [5,0,8,1,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,1,7,3,0] (by decide +kernel))
      (invalid_excluded a [5,0,8,1,7,3,1] (by decide +kernel))
      node_926
      (invalid_excluded a [5,0,8,1,7,3,3] (by decide +kernel))
      node_927
      (invalid_excluded a [5,0,8,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,0,8,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,0,8,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,0,8,1,7,3,8] (by decide +kernel)))

theorem node_928 : Excluded a [5,0,8,1,7,4] :=
  predecessor_excluded a [5,0,8,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_923 : Excluded a [5,0,8,1,7] :=
  branch_excluded a [5,0,8,1,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,1,7,0] (by decide +kernel))
      (invalid_excluded a [5,0,8,1,7,1] (by decide +kernel))
      node_924
      node_925
      node_928
      (invalid_excluded a [5,0,8,1,7,5] (by decide +kernel))
      (invalid_excluded a [5,0,8,1,7,6] (by decide +kernel))
      (invalid_excluded a [5,0,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [5,0,8,1,7,8] (by decide +kernel)))

theorem node_916 : Excluded a [5,0,8,1] :=
  branch_excluded a [5,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [5,0,8,1,1] (by decide +kernel))
      node_917
      node_918
      (invalid_excluded a [5,0,8,1,4] (by decide +kernel))
      (invalid_excluded a [5,0,8,1,5] (by decide +kernel))
      node_922
      node_923
      (invalid_excluded a [5,0,8,1,8] (by decide +kernel)))

theorem node_930 : Excluded a [5,0,8,2,1] :=
  source_excluded a [5,0,8,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_931 : Excluded a [5,0,8,2,3] :=
  predecessor_excluded a [5,0,8,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_932 : Excluded a [5,0,8,2,6] :=
  source_excluded a [5,0,8,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_934 : Excluded a [5,0,8,2,7,1] :=
  source_excluded a [5,0,8,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_938 : Excluded a [5,0,8,2,7,3,1,4,6] :=
  predecessor_excluded a [5,0,8,2,7,3,1,4,6] 2 1 8 6 (by decide) (by decide +kernel)

theorem node_937 : Excluded a [5,0,8,2,7,3,1,4] :=
  branch_excluded a [5,0,8,2,7,3,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,2,7,3,1,4,0] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,3,1,4,1] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,3,1,4,2] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,3,1,4,3] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,3,1,4,4] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,3,1,4,5] (by decide +kernel))
      node_938
      (invalid_excluded a [5,0,8,2,7,3,1,4,7] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,3,1,4,8] (by decide +kernel)))

theorem node_939 : Excluded a [5,0,8,2,7,3,1,6] :=
  predecessor_excluded a [5,0,8,2,7,3,1,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_936 : Excluded a [5,0,8,2,7,3,1] :=
  branch_excluded a [5,0,8,2,7,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,2,7,3,1,0] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,3,1,1] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,3,1,2] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,3,1,3] (by decide +kernel))
      node_937
      (invalid_excluded a [5,0,8,2,7,3,1,5] (by decide +kernel))
      node_939
      (invalid_excluded a [5,0,8,2,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,3,1,8] (by decide +kernel)))

theorem node_940 : Excluded a [5,0,8,2,7,3,4] :=
  source_excluded a [5,0,8,2,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_935 : Excluded a [5,0,8,2,7,3] :=
  branch_excluded a [5,0,8,2,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,2,7,3,0] (by decide +kernel))
      node_936
      (invalid_excluded a [5,0,8,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,3,3] (by decide +kernel))
      node_940
      (invalid_excluded a [5,0,8,2,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,3,8] (by decide +kernel)))

theorem node_941 : Excluded a [5,0,8,2,7,4] :=
  predecessor_excluded a [5,0,8,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_933 : Excluded a [5,0,8,2,7] :=
  branch_excluded a [5,0,8,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,2,7,0] (by decide +kernel))
      node_934
      (invalid_excluded a [5,0,8,2,7,2] (by decide +kernel))
      node_935
      node_941
      (invalid_excluded a [5,0,8,2,7,5] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,6] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,7] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,7,8] (by decide +kernel)))

theorem node_929 : Excluded a [5,0,8,2] :=
  branch_excluded a [5,0,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,2,0] (by decide +kernel))
      node_930
      (invalid_excluded a [5,0,8,2,2] (by decide +kernel))
      node_931
      (invalid_excluded a [5,0,8,2,4] (by decide +kernel))
      (invalid_excluded a [5,0,8,2,5] (by decide +kernel))
      node_932
      node_933
      (invalid_excluded a [5,0,8,2,8] (by decide +kernel)))

theorem node_943 : Excluded a [5,0,8,6,1] :=
  source_excluded a [5,0,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_945 : Excluded a [5,0,8,6,2,1] :=
  source_excluded a [5,0,8,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_946 : Excluded a [5,0,8,6,2,3] :=
  source_excluded a [5,0,8,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_947 : Excluded a [5,0,8,6,2,4] :=
  source_excluded a [5,0,8,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_948 : Excluded a [5,0,8,6,2,7] :=
  source_excluded a [5,0,8,6,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_944 : Excluded a [5,0,8,6,2] :=
  branch_excluded a [5,0,8,6,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,6,2,0] (by decide +kernel))
      node_945
      (invalid_excluded a [5,0,8,6,2,2] (by decide +kernel))
      node_946
      node_947
      (invalid_excluded a [5,0,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,0,8,6,2,6] (by decide +kernel))
      node_948
      (invalid_excluded a [5,0,8,6,2,8] (by decide +kernel)))

theorem node_949 : Excluded a [5,0,8,6,3] :=
  predecessor_excluded a [5,0,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_950 : Excluded a [5,0,8,6,7] :=
  predecessor_excluded a [5,0,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_942 : Excluded a [5,0,8,6] :=
  branch_excluded a [5,0,8,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,6,0] (by decide +kernel))
      node_943
      node_944
      node_949
      (invalid_excluded a [5,0,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,0,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,0,8,6,6] (by decide +kernel))
      node_950
      (invalid_excluded a [5,0,8,6,8] (by decide +kernel)))

theorem node_952 : Excluded a [5,0,8,7,1] :=
  source_excluded a [5,0,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_954 : Excluded a [5,0,8,7,2,1] :=
  source_excluded a [5,0,8,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_955 : Excluded a [5,0,8,7,2,3] :=
  predecessor_excluded a [5,0,8,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_958 : Excluded a [5,0,8,7,2,4,1,3] :=
  source_excluded a [5,0,8,7,2,4,1,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_960 : Excluded a [5,0,8,7,2,4,1,6,3] :=
  source_excluded a [5,0,8,7,2,4,1,6,3] 2 0 8 (by decide) (by decide +kernel)

theorem node_959 : Excluded a [5,0,8,7,2,4,1,6] :=
  branch_excluded a [5,0,8,7,2,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,7,2,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,4,1,6,2] (by decide +kernel))
      node_960
      (invalid_excluded a [5,0,8,7,2,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,4,1,6,8] (by decide +kernel)))

theorem node_957 : Excluded a [5,0,8,7,2,4,1] :=
  branch_excluded a [5,0,8,7,2,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,7,2,4,1,0] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,4,1,1] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,4,1,2] (by decide +kernel))
      node_958
      (invalid_excluded a [5,0,8,7,2,4,1,4] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,4,1,5] (by decide +kernel))
      node_959
      (invalid_excluded a [5,0,8,7,2,4,1,7] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,4,1,8] (by decide +kernel)))

theorem node_961 : Excluded a [5,0,8,7,2,4,3] :=
  source_excluded a [5,0,8,7,2,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_956 : Excluded a [5,0,8,7,2,4] :=
  branch_excluded a [5,0,8,7,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,7,2,4,0] (by decide +kernel))
      node_957
      (invalid_excluded a [5,0,8,7,2,4,2] (by decide +kernel))
      node_961
      (invalid_excluded a [5,0,8,7,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,4,8] (by decide +kernel)))

theorem node_953 : Excluded a [5,0,8,7,2] :=
  branch_excluded a [5,0,8,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,7,2,0] (by decide +kernel))
      node_954
      (invalid_excluded a [5,0,8,7,2,2] (by decide +kernel))
      node_955
      node_956
      (invalid_excluded a [5,0,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,2,8] (by decide +kernel)))

theorem node_963 : Excluded a [5,0,8,7,3,1] :=
  source_excluded a [5,0,8,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_964 : Excluded a [5,0,8,7,3,2] :=
  predecessor_excluded a [5,0,8,7,3,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_965 : Excluded a [5,0,8,7,3,4] :=
  predecessor_excluded a [5,0,8,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_962 : Excluded a [5,0,8,7,3] :=
  branch_excluded a [5,0,8,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,7,3,0] (by decide +kernel))
      node_963
      node_964
      (invalid_excluded a [5,0,8,7,3,3] (by decide +kernel))
      node_965
      (invalid_excluded a [5,0,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,3,8] (by decide +kernel)))

theorem node_966 : Excluded a [5,0,8,7,6] :=
  source_excluded a [5,0,8,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_951 : Excluded a [5,0,8,7] :=
  branch_excluded a [5,0,8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,7,0] (by decide +kernel))
      node_952
      node_953
      node_962
      (invalid_excluded a [5,0,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,5] (by decide +kernel))
      node_966
      (invalid_excluded a [5,0,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,0,8,7,8] (by decide +kernel)))

theorem node_915 : Excluded a [5,0,8] :=
  branch_excluded a [5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,8,0] (by decide +kernel))
      node_916
      node_929
      (invalid_excluded a [5,0,8,3] (by decide +kernel))
      (invalid_excluded a [5,0,8,4] (by decide +kernel))
      (invalid_excluded a [5,0,8,5] (by decide +kernel))
      node_942
      node_951
      (invalid_excluded a [5,0,8,8] (by decide +kernel)))

theorem node_798 : Excluded a [5,0] :=
  branch_excluded a [5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0,0] (by decide +kernel))
      node_799
      (invalid_excluded a [5,0,2] (by decide +kernel))
      (invalid_excluded a [5,0,3] (by decide +kernel))
      node_800
      (invalid_excluded a [5,0,5] (by decide +kernel))
      node_801
      node_857
      node_915)

theorem node_967 : Excluded a [5,3] :=
  source_excluded a [5,3] 1 0 2 (by decide) (by decide +kernel)

theorem node_970 : Excluded a [5,4,0,1] :=
  source_excluded a [5,4,0,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_971 : Excluded a [5,4,0,2] :=
  source_excluded a [5,4,0,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_973 : Excluded a [5,4,0,6,1] :=
  source_excluded a [5,4,0,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_974 : Excluded a [5,4,0,6,2] :=
  source_excluded a [5,4,0,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_975 : Excluded a [5,4,0,6,3] :=
  predecessor_excluded a [5,4,0,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_976 : Excluded a [5,4,0,6,7] :=
  predecessor_excluded a [5,4,0,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_978 : Excluded a [5,4,0,6,8,1] :=
  source_excluded a [5,4,0,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_979 : Excluded a [5,4,0,6,8,2] :=
  predecessor_excluded a [5,4,0,6,8,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_980 : Excluded a [5,4,0,6,8,3] :=
  source_excluded a [5,4,0,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_981 : Excluded a [5,4,0,6,8,7] :=
  source_excluded a [5,4,0,6,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_977 : Excluded a [5,4,0,6,8] :=
  branch_excluded a [5,4,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,6,8,0] (by decide +kernel))
      node_978
      node_979
      node_980
      (invalid_excluded a [5,4,0,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,6] (by decide +kernel))
      node_981
      (invalid_excluded a [5,4,0,6,8,8] (by decide +kernel)))

theorem node_972 : Excluded a [5,4,0,6] :=
  branch_excluded a [5,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,6,0] (by decide +kernel))
      node_973
      node_974
      node_975
      (invalid_excluded a [5,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,6] (by decide +kernel))
      node_976
      node_977)

theorem node_983 : Excluded a [5,4,0,7,1] :=
  source_excluded a [5,4,0,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_984 : Excluded a [5,4,0,7,2] :=
  source_excluded a [5,4,0,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_985 : Excluded a [5,4,0,7,3] :=
  predecessor_excluded a [5,4,0,7,3] 0 3 1 4 (by decide) (by decide +kernel)

theorem node_986 : Excluded a [5,4,0,7,6] :=
  source_excluded a [5,4,0,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_987 : Excluded a [5,4,0,7,8] :=
  predecessor_excluded a [5,4,0,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_982 : Excluded a [5,4,0,7] :=
  branch_excluded a [5,4,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,7,0] (by decide +kernel))
      node_983
      node_984
      node_985
      (invalid_excluded a [5,4,0,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,5] (by decide +kernel))
      node_986
      (invalid_excluded a [5,4,0,7,7] (by decide +kernel))
      node_987)

theorem node_989 : Excluded a [5,4,0,8,1] :=
  source_excluded a [5,4,0,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_990 : Excluded a [5,4,0,8,2] :=
  source_excluded a [5,4,0,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_991 : Excluded a [5,4,0,8,3] :=
  predecessor_excluded a [5,4,0,8,3] 0 3 1 4 (by decide) (by decide +kernel)

theorem node_992 : Excluded a [5,4,0,8,6] :=
  source_excluded a [5,4,0,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_994 : Excluded a [5,4,0,8,7,1] :=
  source_excluded a [5,4,0,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_995 : Excluded a [5,4,0,8,7,2] :=
  predecessor_excluded a [5,4,0,8,7,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_998 : Excluded a [5,4,0,8,7,3,1,2] :=
  predecessor_excluded a [5,4,0,8,7,3,1,2] 1 0 7 2 (by decide) (by decide +kernel)

theorem node_999 : Excluded a [5,4,0,8,7,3,1,6] :=
  predecessor_excluded a [5,4,0,8,7,3,1,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_997 : Excluded a [5,4,0,8,7,3,1] :=
  branch_excluded a [5,4,0,8,7,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,7,3,1,0] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,1,1] (by decide +kernel))
      node_998
      (invalid_excluded a [5,4,0,8,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,1,5] (by decide +kernel))
      node_999
      (invalid_excluded a [5,4,0,8,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,1,8] (by decide +kernel)))

def b_1002 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 0
  | 3 => 8
  | 4 => 7
  | 5 => 3
  | 6 => 2
  | 7 => 1
  | 8 => 6
  | _ => 0

def cert_1002 : LosingRegion (edgeOf a b_1002) 0 :=
  losingMask a b_1002 0 1212468759815673198185472
    (by decide +kernel) (by decide +kernel)

theorem node_1002 : Excluded a [5,4,0,8,7,3,2,1,6] :=
  losing_excluded a [5,4,0,8,7,3,2,1,6] (by decide) b_1002 (by decide +kernel) 1 0 2 cert_1002 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1002 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212468759815673198185472 1 2; decide +kernel)

theorem node_1001 : Excluded a [5,4,0,8,7,3,2,1] :=
  branch_excluded a [5,4,0,8,7,3,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,7,3,2,1,0] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,2,1,1] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,2,1,2] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,2,1,3] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,2,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,2,1,5] (by decide +kernel))
      node_1002
      (invalid_excluded a [5,4,0,8,7,3,2,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,2,1,8] (by decide +kernel)))

theorem node_1003 : Excluded a [5,4,0,8,7,3,2,6] :=
  predecessor_excluded a [5,4,0,8,7,3,2,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_1000 : Excluded a [5,4,0,8,7,3,2] :=
  branch_excluded a [5,4,0,8,7,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,7,3,2,0] (by decide +kernel))
      node_1001
      (invalid_excluded a [5,4,0,8,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,2,5] (by decide +kernel))
      node_1003
      (invalid_excluded a [5,4,0,8,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,2,8] (by decide +kernel)))

theorem node_996 : Excluded a [5,4,0,8,7,3] :=
  branch_excluded a [5,4,0,8,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,7,3,0] (by decide +kernel))
      node_997
      node_1000
      (invalid_excluded a [5,4,0,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,8] (by decide +kernel)))

theorem node_993 : Excluded a [5,4,0,8,7] :=
  branch_excluded a [5,4,0,8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,7,0] (by decide +kernel))
      node_994
      node_995
      node_996
      (invalid_excluded a [5,4,0,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,8] (by decide +kernel)))

theorem node_988 : Excluded a [5,4,0,8] :=
  branch_excluded a [5,4,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,0] (by decide +kernel))
      node_989
      node_990
      node_991
      (invalid_excluded a [5,4,0,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,5] (by decide +kernel))
      node_992
      node_993
      (invalid_excluded a [5,4,0,8,8] (by decide +kernel)))

theorem node_969 : Excluded a [5,4,0] :=
  branch_excluded a [5,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,0] (by decide +kernel))
      node_970
      node_971
      (invalid_excluded a [5,4,0,3] (by decide +kernel))
      (invalid_excluded a [5,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,5] (by decide +kernel))
      node_972
      node_982
      node_988)

theorem node_1004 : Excluded a [5,4,1] :=
  predecessor_excluded a [5,4,1] 0 4 2 1 (by decide) (by decide +kernel)

theorem node_1006 : Excluded a [5,4,6,0] :=
  predecessor_excluded a [5,4,6,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1007 : Excluded a [5,4,6,1] :=
  source_excluded a [5,4,6,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1008 : Excluded a [5,4,6,2] :=
  source_excluded a [5,4,6,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1009 : Excluded a [5,4,6,7] :=
  predecessor_excluded a [5,4,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_1011 : Excluded a [5,4,6,8,0] :=
  source_excluded a [5,4,6,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1012 : Excluded a [5,4,6,8,1] :=
  source_excluded a [5,4,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1013 : Excluded a [5,4,6,8,2] :=
  source_excluded a [5,4,6,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1014 : Excluded a [5,4,6,8,3] :=
  predecessor_excluded a [5,4,6,8,3] 0 3 1 4 (by decide) (by decide +kernel)

theorem node_1017 : Excluded a [5,4,6,8,7,0,1] :=
  predecessor_excluded a [5,4,6,8,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

def b_1020 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 6
  | 3 => 8
  | 4 => 7
  | 5 => 0
  | 6 => 2
  | 7 => 1
  | 8 => 3
  | _ => 0

def cert_1020 : LosingRegion (edgeOf a b_1020) 0 :=
  losingMask a b_1020 0 1212549669203391171007488
    (by decide +kernel) (by decide +kernel)

theorem node_1020 : Excluded a [5,4,6,8,7,0,2,1,3] :=
  losing_excluded a [5,4,6,8,7,0,2,1,3] (by decide) b_1020 (by decide +kernel) 1 0 3 cert_1020 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1020 1 0 ∧ 3 ≠ 1 ∧ maskRegion 1212549669203391171007488 1 3; decide +kernel)

theorem node_1019 : Excluded a [5,4,6,8,7,0,2,1] :=
  branch_excluded a [5,4,6,8,7,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,6,8,7,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,1,2] (by decide +kernel))
      node_1020
      (invalid_excluded a [5,4,6,8,7,0,2,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,1,8] (by decide +kernel)))

theorem node_1021 : Excluded a [5,4,6,8,7,0,2,3] :=
  source_excluded a [5,4,6,8,7,0,2,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_1018 : Excluded a [5,4,6,8,7,0,2] :=
  branch_excluded a [5,4,6,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,6,8,7,0,2,0] (by decide +kernel))
      node_1019
      (invalid_excluded a [5,4,6,8,7,0,2,2] (by decide +kernel))
      node_1021
      (invalid_excluded a [5,4,6,8,7,0,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,2,8] (by decide +kernel)))

theorem node_1022 : Excluded a [5,4,6,8,7,0,3] :=
  source_excluded a [5,4,6,8,7,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1016 : Excluded a [5,4,6,8,7,0] :=
  branch_excluded a [5,4,6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,6,8,7,0,0] (by decide +kernel))
      node_1017
      node_1018
      node_1022
      (invalid_excluded a [5,4,6,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,0,8] (by decide +kernel)))

theorem node_1023 : Excluded a [5,4,6,8,7,1] :=
  source_excluded a [5,4,6,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1024 : Excluded a [5,4,6,8,7,2] :=
  source_excluded a [5,4,6,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1025 : Excluded a [5,4,6,8,7,3] :=
  source_excluded a [5,4,6,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1015 : Excluded a [5,4,6,8,7] :=
  branch_excluded a [5,4,6,8,7] (by decide)
    (fin9_cases _
      node_1016
      node_1023
      node_1024
      node_1025
      (invalid_excluded a [5,4,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,8] (by decide +kernel)))

theorem node_1010 : Excluded a [5,4,6,8] :=
  branch_excluded a [5,4,6,8] (by decide)
    (fin9_cases _
      node_1011
      node_1012
      node_1013
      node_1014
      (invalid_excluded a [5,4,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,6] (by decide +kernel))
      node_1015
      (invalid_excluded a [5,4,6,8,8] (by decide +kernel)))

theorem node_1005 : Excluded a [5,4,6] :=
  branch_excluded a [5,4,6] (by decide)
    (fin9_cases _
      node_1006
      node_1007
      node_1008
      (invalid_excluded a [5,4,6,3] (by decide +kernel))
      (invalid_excluded a [5,4,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,6] (by decide +kernel))
      node_1009
      node_1010)

theorem node_1027 : Excluded a [5,4,7,0] :=
  predecessor_excluded a [5,4,7,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1028 : Excluded a [5,4,7,1] :=
  source_excluded a [5,4,7,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1029 : Excluded a [5,4,7,2] :=
  source_excluded a [5,4,7,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1031 : Excluded a [5,4,7,6,0] :=
  source_excluded a [5,4,7,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1032 : Excluded a [5,4,7,6,1] :=
  source_excluded a [5,4,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1033 : Excluded a [5,4,7,6,2] :=
  source_excluded a [5,4,7,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1034 : Excluded a [5,4,7,6,3] :=
  predecessor_excluded a [5,4,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1036 : Excluded a [5,4,7,6,8,0] :=
  predecessor_excluded a [5,4,7,6,8,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_1037 : Excluded a [5,4,7,6,8,1] :=
  source_excluded a [5,4,7,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1038 : Excluded a [5,4,7,6,8,2] :=
  predecessor_excluded a [5,4,7,6,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1039 : Excluded a [5,4,7,6,8,3] :=
  source_excluded a [5,4,7,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1035 : Excluded a [5,4,7,6,8] :=
  branch_excluded a [5,4,7,6,8] (by decide)
    (fin9_cases _
      node_1036
      node_1037
      node_1038
      node_1039
      (invalid_excluded a [5,4,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,8] (by decide +kernel)))

theorem node_1030 : Excluded a [5,4,7,6] :=
  branch_excluded a [5,4,7,6] (by decide)
    (fin9_cases _
      node_1031
      node_1032
      node_1033
      node_1034
      (invalid_excluded a [5,4,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,7] (by decide +kernel))
      node_1035)

theorem node_1040 : Excluded a [5,4,7,8] :=
  predecessor_excluded a [5,4,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_1026 : Excluded a [5,4,7] :=
  branch_excluded a [5,4,7] (by decide)
    (fin9_cases _
      node_1027
      node_1028
      node_1029
      (invalid_excluded a [5,4,7,3] (by decide +kernel))
      (invalid_excluded a [5,4,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,5] (by decide +kernel))
      node_1030
      (invalid_excluded a [5,4,7,7] (by decide +kernel))
      node_1040)

theorem node_1042 : Excluded a [5,4,8,0] :=
  predecessor_excluded a [5,4,8,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1043 : Excluded a [5,4,8,1] :=
  source_excluded a [5,4,8,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1044 : Excluded a [5,4,8,2] :=
  source_excluded a [5,4,8,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1046 : Excluded a [5,4,8,6,0] :=
  source_excluded a [5,4,8,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1047 : Excluded a [5,4,8,6,1] :=
  source_excluded a [5,4,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1048 : Excluded a [5,4,8,6,2] :=
  source_excluded a [5,4,8,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1049 : Excluded a [5,4,8,6,3] :=
  predecessor_excluded a [5,4,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1050 : Excluded a [5,4,8,6,7] :=
  predecessor_excluded a [5,4,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1045 : Excluded a [5,4,8,6] :=
  branch_excluded a [5,4,8,6] (by decide)
    (fin9_cases _
      node_1046
      node_1047
      node_1048
      node_1049
      (invalid_excluded a [5,4,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,8,6,6] (by decide +kernel))
      node_1050
      (invalid_excluded a [5,4,8,6,8] (by decide +kernel)))

theorem node_1052 : Excluded a [5,4,8,7,0] :=
  source_excluded a [5,4,8,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1053 : Excluded a [5,4,8,7,1] :=
  source_excluded a [5,4,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1054 : Excluded a [5,4,8,7,2] :=
  source_excluded a [5,4,8,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1055 : Excluded a [5,4,8,7,3] :=
  predecessor_excluded a [5,4,8,7,3] 0 3 1 4 (by decide) (by decide +kernel)

theorem node_1056 : Excluded a [5,4,8,7,6] :=
  source_excluded a [5,4,8,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1051 : Excluded a [5,4,8,7] :=
  branch_excluded a [5,4,8,7] (by decide)
    (fin9_cases _
      node_1052
      node_1053
      node_1054
      node_1055
      (invalid_excluded a [5,4,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,5] (by decide +kernel))
      node_1056
      (invalid_excluded a [5,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,8] (by decide +kernel)))

theorem node_1041 : Excluded a [5,4,8] :=
  branch_excluded a [5,4,8] (by decide)
    (fin9_cases _
      node_1042
      node_1043
      node_1044
      (invalid_excluded a [5,4,8,3] (by decide +kernel))
      (invalid_excluded a [5,4,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,5] (by decide +kernel))
      node_1045
      node_1051
      (invalid_excluded a [5,4,8,8] (by decide +kernel)))

theorem node_968 : Excluded a [5,4] :=
  branch_excluded a [5,4] (by decide)
    (fin9_cases _
      node_969
      node_1004
      (invalid_excluded a [5,4,2] (by decide +kernel))
      (invalid_excluded a [5,4,3] (by decide +kernel))
      (invalid_excluded a [5,4,4] (by decide +kernel))
      (invalid_excluded a [5,4,5] (by decide +kernel))
      node_1005
      node_1026
      node_1041)

theorem node_1057 : Excluded a [5,6] :=
  predecessor_excluded a [5,6] 2 6 0 1 (by decide) (by decide +kernel)

theorem node_1060 : Excluded a [5,7,0,1] :=
  predecessor_excluded a [5,7,0,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_1062 : Excluded a [5,7,0,2,1] :=
  source_excluded a [5,7,0,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1063 : Excluded a [5,7,0,2,3] :=
  predecessor_excluded a [5,7,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1064 : Excluded a [5,7,0,2,6] :=
  source_excluded a [5,7,0,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1066 : Excluded a [5,7,0,2,8,1] :=
  source_excluded a [5,7,0,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1068 : Excluded a [5,7,0,2,8,3,1] :=
  source_excluded a [5,7,0,2,8,3,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1069 : Excluded a [5,7,0,2,8,3,4] :=
  predecessor_excluded a [5,7,0,2,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1067 : Excluded a [5,7,0,2,8,3] :=
  branch_excluded a [5,7,0,2,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,2,8,3,0] (by decide +kernel))
      node_1068
      (invalid_excluded a [5,7,0,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,3,3] (by decide +kernel))
      node_1069
      (invalid_excluded a [5,7,0,2,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,3,8] (by decide +kernel)))

theorem node_1071 : Excluded a [5,7,0,2,8,4,1] :=
  source_excluded a [5,7,0,2,8,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1074 : Excluded a [5,7,0,2,8,4,3,1,6] :=
  predecessor_excluded a [5,7,0,2,8,4,3,1,6] 0 6 4 8 (by decide) (by decide +kernel)

theorem node_1073 : Excluded a [5,7,0,2,8,4,3,1] :=
  branch_excluded a [5,7,0,2,8,4,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,2,8,4,3,1,0] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,1,1] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,1,2] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,1,3] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,1,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,1,5] (by decide +kernel))
      node_1074
      (invalid_excluded a [5,7,0,2,8,4,3,1,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,1,8] (by decide +kernel)))

theorem node_1076 : Excluded a [5,7,0,2,8,4,3,6,1] :=
  source_excluded a [5,7,0,2,8,4,3,6,1] 8 2 0 (by decide) (by decide +kernel)

theorem node_1075 : Excluded a [5,7,0,2,8,4,3,6] :=
  branch_excluded a [5,7,0,2,8,4,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,2,8,4,3,6,0] (by decide +kernel))
      node_1076
      (invalid_excluded a [5,7,0,2,8,4,3,6,2] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,6,8] (by decide +kernel)))

theorem node_1072 : Excluded a [5,7,0,2,8,4,3] :=
  branch_excluded a [5,7,0,2,8,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,2,8,4,3,0] (by decide +kernel))
      node_1073
      (invalid_excluded a [5,7,0,2,8,4,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,5] (by decide +kernel))
      node_1075
      (invalid_excluded a [5,7,0,2,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,8] (by decide +kernel)))

theorem node_1070 : Excluded a [5,7,0,2,8,4] :=
  branch_excluded a [5,7,0,2,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,2,8,4,0] (by decide +kernel))
      node_1071
      (invalid_excluded a [5,7,0,2,8,4,2] (by decide +kernel))
      node_1072
      (invalid_excluded a [5,7,0,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,8] (by decide +kernel)))

theorem node_1065 : Excluded a [5,7,0,2,8] :=
  branch_excluded a [5,7,0,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,2,8,0] (by decide +kernel))
      node_1066
      (invalid_excluded a [5,7,0,2,8,2] (by decide +kernel))
      node_1067
      node_1070
      (invalid_excluded a [5,7,0,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,8] (by decide +kernel)))

theorem node_1061 : Excluded a [5,7,0,2] :=
  branch_excluded a [5,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,2,0] (by decide +kernel))
      node_1062
      (invalid_excluded a [5,7,0,2,2] (by decide +kernel))
      node_1063
      (invalid_excluded a [5,7,0,2,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,5] (by decide +kernel))
      node_1064
      (invalid_excluded a [5,7,0,2,7] (by decide +kernel))
      node_1065)

theorem node_1078 : Excluded a [5,7,0,6,1] :=
  source_excluded a [5,7,0,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1080 : Excluded a [5,7,0,6,2,1] :=
  source_excluded a [5,7,0,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1081 : Excluded a [5,7,0,6,2,3] :=
  source_excluded a [5,7,0,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1082 : Excluded a [5,7,0,6,2,4] :=
  source_excluded a [5,7,0,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1084 : Excluded a [5,7,0,6,2,8,1] :=
  source_excluded a [5,7,0,6,2,8,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1087 : Excluded a [5,7,0,6,2,8,3,1,4] :=
  predecessor_excluded a [5,7,0,6,2,8,3,1,4] 1 5 8 0 (by decide) (by decide +kernel)

theorem node_1086 : Excluded a [5,7,0,6,2,8,3,1] :=
  branch_excluded a [5,7,0,6,2,8,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,6,2,8,3,1,0] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,3,1,1] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,3,1,2] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,3,1,3] (by decide +kernel))
      node_1087
      (invalid_excluded a [5,7,0,6,2,8,3,1,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,3,1,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,3,1,8] (by decide +kernel)))

theorem node_1088 : Excluded a [5,7,0,6,2,8,3,4] :=
  predecessor_excluded a [5,7,0,6,2,8,3,4] 0 4 6 7 (by decide) (by decide +kernel)

theorem node_1085 : Excluded a [5,7,0,6,2,8,3] :=
  branch_excluded a [5,7,0,6,2,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,6,2,8,3,0] (by decide +kernel))
      node_1086
      (invalid_excluded a [5,7,0,6,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,3,3] (by decide +kernel))
      node_1088
      (invalid_excluded a [5,7,0,6,2,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,3,8] (by decide +kernel)))

theorem node_1089 : Excluded a [5,7,0,6,2,8,4] :=
  source_excluded a [5,7,0,6,2,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1083 : Excluded a [5,7,0,6,2,8] :=
  branch_excluded a [5,7,0,6,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,6,2,8,0] (by decide +kernel))
      node_1084
      (invalid_excluded a [5,7,0,6,2,8,2] (by decide +kernel))
      node_1085
      node_1089
      (invalid_excluded a [5,7,0,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,8] (by decide +kernel)))

theorem node_1079 : Excluded a [5,7,0,6,2] :=
  branch_excluded a [5,7,0,6,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,6,2,0] (by decide +kernel))
      node_1080
      (invalid_excluded a [5,7,0,6,2,2] (by decide +kernel))
      node_1081
      node_1082
      (invalid_excluded a [5,7,0,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,7] (by decide +kernel))
      node_1083)

theorem node_1090 : Excluded a [5,7,0,6,3] :=
  predecessor_excluded a [5,7,0,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1092 : Excluded a [5,7,0,6,8,1] :=
  source_excluded a [5,7,0,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1093 : Excluded a [5,7,0,6,8,2] :=
  predecessor_excluded a [5,7,0,6,8,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_1094 : Excluded a [5,7,0,6,8,3] :=
  source_excluded a [5,7,0,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1095 : Excluded a [5,7,0,6,8,4] :=
  source_excluded a [5,7,0,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1091 : Excluded a [5,7,0,6,8] :=
  branch_excluded a [5,7,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,6,8,0] (by decide +kernel))
      node_1092
      node_1093
      node_1094
      node_1095
      (invalid_excluded a [5,7,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,8,8] (by decide +kernel)))

theorem node_1077 : Excluded a [5,7,0,6] :=
  branch_excluded a [5,7,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,6,0] (by decide +kernel))
      node_1078
      node_1079
      node_1090
      (invalid_excluded a [5,7,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,7] (by decide +kernel))
      node_1091)

theorem node_1097 : Excluded a [5,7,0,8,1] :=
  source_excluded a [5,7,0,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1099 : Excluded a [5,7,0,8,2,1] :=
  source_excluded a [5,7,0,8,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1100 : Excluded a [5,7,0,8,2,3] :=
  predecessor_excluded a [5,7,0,8,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_1102 : Excluded a [5,7,0,8,2,4,1] :=
  source_excluded a [5,7,0,8,2,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1103 : Excluded a [5,7,0,8,2,4,3] :=
  predecessor_excluded a [5,7,0,8,2,4,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_1101 : Excluded a [5,7,0,8,2,4] :=
  branch_excluded a [5,7,0,8,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,8,2,4,0] (by decide +kernel))
      node_1102
      (invalid_excluded a [5,7,0,8,2,4,2] (by decide +kernel))
      node_1103
      (invalid_excluded a [5,7,0,8,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,2,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,2,4,8] (by decide +kernel)))

theorem node_1098 : Excluded a [5,7,0,8,2] :=
  branch_excluded a [5,7,0,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,8,2,0] (by decide +kernel))
      node_1099
      (invalid_excluded a [5,7,0,8,2,2] (by decide +kernel))
      node_1100
      node_1101
      (invalid_excluded a [5,7,0,8,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,2,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,2,8] (by decide +kernel)))

theorem node_1105 : Excluded a [5,7,0,8,3,1] :=
  source_excluded a [5,7,0,8,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1106 : Excluded a [5,7,0,8,3,2] :=
  predecessor_excluded a [5,7,0,8,3,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_1107 : Excluded a [5,7,0,8,3,4] :=
  predecessor_excluded a [5,7,0,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1104 : Excluded a [5,7,0,8,3] :=
  branch_excluded a [5,7,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,8,3,0] (by decide +kernel))
      node_1105
      node_1106
      (invalid_excluded a [5,7,0,8,3,3] (by decide +kernel))
      node_1107
      (invalid_excluded a [5,7,0,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,8] (by decide +kernel)))

theorem node_1108 : Excluded a [5,7,0,8,6] :=
  source_excluded a [5,7,0,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1096 : Excluded a [5,7,0,8] :=
  branch_excluded a [5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,8,0] (by decide +kernel))
      node_1097
      node_1098
      node_1104
      (invalid_excluded a [5,7,0,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,5] (by decide +kernel))
      node_1108
      (invalid_excluded a [5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,8] (by decide +kernel)))

theorem node_1059 : Excluded a [5,7,0] :=
  branch_excluded a [5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,0] (by decide +kernel))
      node_1060
      node_1061
      (invalid_excluded a [5,7,0,3] (by decide +kernel))
      (invalid_excluded a [5,7,0,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,5] (by decide +kernel))
      node_1077
      (invalid_excluded a [5,7,0,7] (by decide +kernel))
      node_1096)

theorem node_1110 : Excluded a [5,7,1,0] :=
  predecessor_excluded a [5,7,1,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1111 : Excluded a [5,7,1,2] :=
  predecessor_excluded a [5,7,1,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_1113 : Excluded a [5,7,1,6,0] :=
  source_excluded a [5,7,1,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1117 : Excluded a [5,7,1,6,2,0,3,4] :=
  predecessor_excluded a [5,7,1,6,2,0,3,4] 0 4 6 7 (by decide) (by decide +kernel)

theorem node_1116 : Excluded a [5,7,1,6,2,0,3] :=
  branch_excluded a [5,7,1,6,2,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,1,6,2,0,3,0] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,0,3,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,0,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,0,3,3] (by decide +kernel))
      node_1117
      (invalid_excluded a [5,7,1,6,2,0,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,0,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,0,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,0,3,8] (by decide +kernel)))

theorem node_1118 : Excluded a [5,7,1,6,2,0,4] :=
  source_excluded a [5,7,1,6,2,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1119 : Excluded a [5,7,1,6,2,0,8] :=
  source_excluded a [5,7,1,6,2,0,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_1115 : Excluded a [5,7,1,6,2,0] :=
  branch_excluded a [5,7,1,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,1,6,2,0,0] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,0,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,0,2] (by decide +kernel))
      node_1116
      node_1118
      (invalid_excluded a [5,7,1,6,2,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,0,7] (by decide +kernel))
      node_1119)

theorem node_1120 : Excluded a [5,7,1,6,2,3] :=
  source_excluded a [5,7,1,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1121 : Excluded a [5,7,1,6,2,4] :=
  source_excluded a [5,7,1,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1123 : Excluded a [5,7,1,6,2,8,0] :=
  predecessor_excluded a [5,7,1,6,2,8,0] 1 0 5 6 (by decide) (by decide +kernel)

theorem node_1125 : Excluded a [5,7,1,6,2,8,3,0] :=
  source_excluded a [5,7,1,6,2,8,3,0] 7 1 8 (by decide) (by decide +kernel)

theorem node_1126 : Excluded a [5,7,1,6,2,8,3,4] :=
  predecessor_excluded a [5,7,1,6,2,8,3,4] 0 4 6 7 (by decide) (by decide +kernel)

theorem node_1124 : Excluded a [5,7,1,6,2,8,3] :=
  branch_excluded a [5,7,1,6,2,8,3] (by decide)
    (fin9_cases _
      node_1125
      (invalid_excluded a [5,7,1,6,2,8,3,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,3,3] (by decide +kernel))
      node_1126
      (invalid_excluded a [5,7,1,6,2,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,3,8] (by decide +kernel)))

theorem node_1127 : Excluded a [5,7,1,6,2,8,4] :=
  source_excluded a [5,7,1,6,2,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1122 : Excluded a [5,7,1,6,2,8] :=
  branch_excluded a [5,7,1,6,2,8] (by decide)
    (fin9_cases _
      node_1123
      (invalid_excluded a [5,7,1,6,2,8,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,2] (by decide +kernel))
      node_1124
      node_1127
      (invalid_excluded a [5,7,1,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,8] (by decide +kernel)))

theorem node_1114 : Excluded a [5,7,1,6,2] :=
  branch_excluded a [5,7,1,6,2] (by decide)
    (fin9_cases _
      node_1115
      (invalid_excluded a [5,7,1,6,2,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,2] (by decide +kernel))
      node_1120
      node_1121
      (invalid_excluded a [5,7,1,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,7] (by decide +kernel))
      node_1122)

theorem node_1128 : Excluded a [5,7,1,6,3] :=
  predecessor_excluded a [5,7,1,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1130 : Excluded a [5,7,1,6,8,0] :=
  predecessor_excluded a [5,7,1,6,8,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_1131 : Excluded a [5,7,1,6,8,2] :=
  predecessor_excluded a [5,7,1,6,8,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_1132 : Excluded a [5,7,1,6,8,3] :=
  source_excluded a [5,7,1,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1133 : Excluded a [5,7,1,6,8,4] :=
  source_excluded a [5,7,1,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1129 : Excluded a [5,7,1,6,8] :=
  branch_excluded a [5,7,1,6,8] (by decide)
    (fin9_cases _
      node_1130
      (invalid_excluded a [5,7,1,6,8,1] (by decide +kernel))
      node_1131
      node_1132
      node_1133
      (invalid_excluded a [5,7,1,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,8,8] (by decide +kernel)))

theorem node_1112 : Excluded a [5,7,1,6] :=
  branch_excluded a [5,7,1,6] (by decide)
    (fin9_cases _
      node_1113
      (invalid_excluded a [5,7,1,6,1] (by decide +kernel))
      node_1114
      node_1128
      (invalid_excluded a [5,7,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,7] (by decide +kernel))
      node_1129)

theorem node_1135 : Excluded a [5,7,1,8,0] :=
  source_excluded a [5,7,1,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1138 : Excluded a [5,7,1,8,2,0,3] :=
  predecessor_excluded a [5,7,1,8,2,0,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_1140 : Excluded a [5,7,1,8,2,0,4,3] :=
  source_excluded a [5,7,1,8,2,0,4,3] 7 0 3 (by decide) (by decide +kernel)

def b_1142 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 7
  | 2 => 1
  | 3 => 8
  | 4 => 2
  | 5 => 0
  | 6 => 4
  | 7 => 6
  | 8 => 3
  | _ => 0

def cert_1142 : LosingRegion (edgeOf a b_1142) 0 :=
  losingMask a b_1142 0 1212542679616769492196352
    (by decide +kernel) (by decide +kernel)

theorem node_1142 : Excluded a [5,7,1,8,2,0,4,6,3] :=
  losing_excluded a [5,7,1,8,2,0,4,6,3] (by decide) b_1142 (by decide +kernel) 1 0 2 cert_1142 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1142 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212542679616769492196352 1 2; decide +kernel)

theorem node_1141 : Excluded a [5,7,1,8,2,0,4,6] :=
  branch_excluded a [5,7,1,8,2,0,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,1,8,2,0,4,6,0] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,4,6,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,4,6,2] (by decide +kernel))
      node_1142
      (invalid_excluded a [5,7,1,8,2,0,4,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,4,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,4,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,4,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,4,6,8] (by decide +kernel)))

theorem node_1139 : Excluded a [5,7,1,8,2,0,4] :=
  branch_excluded a [5,7,1,8,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,1,8,2,0,4,0] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,4,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,4,2] (by decide +kernel))
      node_1140
      (invalid_excluded a [5,7,1,8,2,0,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,4,5] (by decide +kernel))
      node_1141
      (invalid_excluded a [5,7,1,8,2,0,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,4,8] (by decide +kernel)))

theorem node_1137 : Excluded a [5,7,1,8,2,0] :=
  branch_excluded a [5,7,1,8,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,1,8,2,0,0] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,2] (by decide +kernel))
      node_1138
      node_1139
      (invalid_excluded a [5,7,1,8,2,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,0,8] (by decide +kernel)))

theorem node_1143 : Excluded a [5,7,1,8,2,3] :=
  predecessor_excluded a [5,7,1,8,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_1146 : Excluded a [5,7,1,8,2,4,0,3] :=
  source_excluded a [5,7,1,8,2,4,0,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_1147 : Excluded a [5,7,1,8,2,4,0,6] :=
  predecessor_excluded a [5,7,1,8,2,4,0,6] 1 0 7 6 (by decide) (by decide +kernel)

theorem node_1145 : Excluded a [5,7,1,8,2,4,0] :=
  branch_excluded a [5,7,1,8,2,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,1,8,2,4,0,0] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,4,0,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,4,0,2] (by decide +kernel))
      node_1146
      (invalid_excluded a [5,7,1,8,2,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,4,0,5] (by decide +kernel))
      node_1147
      (invalid_excluded a [5,7,1,8,2,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,4,0,8] (by decide +kernel)))

theorem node_1148 : Excluded a [5,7,1,8,2,4,3] :=
  predecessor_excluded a [5,7,1,8,2,4,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_1144 : Excluded a [5,7,1,8,2,4] :=
  branch_excluded a [5,7,1,8,2,4] (by decide)
    (fin9_cases _
      node_1145
      (invalid_excluded a [5,7,1,8,2,4,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,4,2] (by decide +kernel))
      node_1148
      (invalid_excluded a [5,7,1,8,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,4,8] (by decide +kernel)))

theorem node_1136 : Excluded a [5,7,1,8,2] :=
  branch_excluded a [5,7,1,8,2] (by decide)
    (fin9_cases _
      node_1137
      (invalid_excluded a [5,7,1,8,2,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,2] (by decide +kernel))
      node_1143
      node_1144
      (invalid_excluded a [5,7,1,8,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2,8] (by decide +kernel)))

theorem node_1151 : Excluded a [5,7,1,8,3,0,2] :=
  source_excluded a [5,7,1,8,3,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_1153 : Excluded a [5,7,1,8,3,0,4,2] :=
  source_excluded a [5,7,1,8,3,0,4,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_1155 : Excluded a [5,7,1,8,3,0,4,6,2] :=
  predecessor_excluded a [5,7,1,8,3,0,4,6,2] 3 1 8 2 (by decide) (by decide +kernel)

theorem node_1154 : Excluded a [5,7,1,8,3,0,4,6] :=
  branch_excluded a [5,7,1,8,3,0,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,1,8,3,0,4,6,0] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,0,4,6,1] (by decide +kernel))
      node_1155
      (invalid_excluded a [5,7,1,8,3,0,4,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,0,4,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,0,4,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,0,4,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,0,4,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,0,4,6,8] (by decide +kernel)))

theorem node_1152 : Excluded a [5,7,1,8,3,0,4] :=
  branch_excluded a [5,7,1,8,3,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,1,8,3,0,4,0] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,0,4,1] (by decide +kernel))
      node_1153
      (invalid_excluded a [5,7,1,8,3,0,4,3] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,0,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,0,4,5] (by decide +kernel))
      node_1154
      (invalid_excluded a [5,7,1,8,3,0,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,0,4,8] (by decide +kernel)))

theorem node_1150 : Excluded a [5,7,1,8,3,0] :=
  branch_excluded a [5,7,1,8,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,1,8,3,0,0] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,0,1] (by decide +kernel))
      node_1151
      (invalid_excluded a [5,7,1,8,3,0,3] (by decide +kernel))
      node_1152
      (invalid_excluded a [5,7,1,8,3,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,0,8] (by decide +kernel)))

theorem node_1156 : Excluded a [5,7,1,8,3,2] :=
  predecessor_excluded a [5,7,1,8,3,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_1157 : Excluded a [5,7,1,8,3,4] :=
  predecessor_excluded a [5,7,1,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1149 : Excluded a [5,7,1,8,3] :=
  branch_excluded a [5,7,1,8,3] (by decide)
    (fin9_cases _
      node_1150
      (invalid_excluded a [5,7,1,8,3,1] (by decide +kernel))
      node_1156
      (invalid_excluded a [5,7,1,8,3,3] (by decide +kernel))
      node_1157
      (invalid_excluded a [5,7,1,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,8] (by decide +kernel)))

theorem node_1158 : Excluded a [5,7,1,8,6] :=
  source_excluded a [5,7,1,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1134 : Excluded a [5,7,1,8] :=
  branch_excluded a [5,7,1,8] (by decide)
    (fin9_cases _
      node_1135
      (invalid_excluded a [5,7,1,8,1] (by decide +kernel))
      node_1136
      node_1149
      (invalid_excluded a [5,7,1,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,5] (by decide +kernel))
      node_1158
      (invalid_excluded a [5,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,8] (by decide +kernel)))

theorem node_1109 : Excluded a [5,7,1] :=
  branch_excluded a [5,7,1] (by decide)
    (fin9_cases _
      node_1110
      (invalid_excluded a [5,7,1,1] (by decide +kernel))
      node_1111
      (invalid_excluded a [5,7,1,3] (by decide +kernel))
      (invalid_excluded a [5,7,1,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,5] (by decide +kernel))
      node_1112
      (invalid_excluded a [5,7,1,7] (by decide +kernel))
      node_1134)

theorem node_1159 : Excluded a [5,7,4] :=
  source_excluded a [5,7,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1161 : Excluded a [5,7,6,0] :=
  predecessor_excluded a [5,7,6,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1163 : Excluded a [5,7,6,1,0] :=
  source_excluded a [5,7,6,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1164 : Excluded a [5,7,6,1,2] :=
  predecessor_excluded a [5,7,6,1,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_1167 : Excluded a [5,7,6,1,3,0,2] :=
  source_excluded a [5,7,6,1,3,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_1168 : Excluded a [5,7,6,1,3,0,4] :=
  predecessor_excluded a [5,7,6,1,3,0,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_1169 : Excluded a [5,7,6,1,3,0,8] :=
  source_excluded a [5,7,6,1,3,0,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_1166 : Excluded a [5,7,6,1,3,0] :=
  branch_excluded a [5,7,6,1,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,6,1,3,0,0] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,0,1] (by decide +kernel))
      node_1167
      (invalid_excluded a [5,7,6,1,3,0,3] (by decide +kernel))
      node_1168
      (invalid_excluded a [5,7,6,1,3,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,0,7] (by decide +kernel))
      node_1169)

theorem node_1170 : Excluded a [5,7,6,1,3,2] :=
  source_excluded a [5,7,6,1,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1171 : Excluded a [5,7,6,1,3,4] :=
  predecessor_excluded a [5,7,6,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1173 : Excluded a [5,7,6,1,3,8,0] :=
  predecessor_excluded a [5,7,6,1,3,8,0] 1 0 5 6 (by decide) (by decide +kernel)

theorem node_1174 : Excluded a [5,7,6,1,3,8,2] :=
  source_excluded a [5,7,6,1,3,8,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_1175 : Excluded a [5,7,6,1,3,8,4] :=
  predecessor_excluded a [5,7,6,1,3,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_1172 : Excluded a [5,7,6,1,3,8] :=
  branch_excluded a [5,7,6,1,3,8] (by decide)
    (fin9_cases _
      node_1173
      (invalid_excluded a [5,7,6,1,3,8,1] (by decide +kernel))
      node_1174
      (invalid_excluded a [5,7,6,1,3,8,3] (by decide +kernel))
      node_1175
      (invalid_excluded a [5,7,6,1,3,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,8,8] (by decide +kernel)))

theorem node_1165 : Excluded a [5,7,6,1,3] :=
  branch_excluded a [5,7,6,1,3] (by decide)
    (fin9_cases _
      node_1166
      (invalid_excluded a [5,7,6,1,3,1] (by decide +kernel))
      node_1170
      (invalid_excluded a [5,7,6,1,3,3] (by decide +kernel))
      node_1171
      (invalid_excluded a [5,7,6,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,7] (by decide +kernel))
      node_1172)

theorem node_1177 : Excluded a [5,7,6,1,8,0] :=
  predecessor_excluded a [5,7,6,1,8,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_1178 : Excluded a [5,7,6,1,8,2] :=
  source_excluded a [5,7,6,1,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1179 : Excluded a [5,7,6,1,8,3] :=
  source_excluded a [5,7,6,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1182 : Excluded a [5,7,6,1,8,4,0,2] :=
  source_excluded a [5,7,6,1,8,4,0,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_1183 : Excluded a [5,7,6,1,8,4,0,3] :=
  predecessor_excluded a [5,7,6,1,8,4,0,3] 0 3 1 7 (by decide) (by decide +kernel)

theorem node_1181 : Excluded a [5,7,6,1,8,4,0] :=
  branch_excluded a [5,7,6,1,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,6,1,8,4,0,0] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,0,1] (by decide +kernel))
      node_1182
      node_1183
      (invalid_excluded a [5,7,6,1,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,0,8] (by decide +kernel)))

theorem node_1184 : Excluded a [5,7,6,1,8,4,2] :=
  source_excluded a [5,7,6,1,8,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_1185 : Excluded a [5,7,6,1,8,4,3] :=
  source_excluded a [5,7,6,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1180 : Excluded a [5,7,6,1,8,4] :=
  branch_excluded a [5,7,6,1,8,4] (by decide)
    (fin9_cases _
      node_1181
      (invalid_excluded a [5,7,6,1,8,4,1] (by decide +kernel))
      node_1184
      node_1185
      (invalid_excluded a [5,7,6,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,8] (by decide +kernel)))

theorem node_1176 : Excluded a [5,7,6,1,8] :=
  branch_excluded a [5,7,6,1,8] (by decide)
    (fin9_cases _
      node_1177
      (invalid_excluded a [5,7,6,1,8,1] (by decide +kernel))
      node_1178
      node_1179
      node_1180
      (invalid_excluded a [5,7,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,8] (by decide +kernel)))

theorem node_1162 : Excluded a [5,7,6,1] :=
  branch_excluded a [5,7,6,1] (by decide)
    (fin9_cases _
      node_1163
      (invalid_excluded a [5,7,6,1,1] (by decide +kernel))
      node_1164
      node_1165
      (invalid_excluded a [5,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,7] (by decide +kernel))
      node_1176)

theorem node_1187 : Excluded a [5,7,6,2,0] :=
  source_excluded a [5,7,6,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1188 : Excluded a [5,7,6,2,1] :=
  source_excluded a [5,7,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1189 : Excluded a [5,7,6,2,3] :=
  predecessor_excluded a [5,7,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1191 : Excluded a [5,7,6,2,8,0] :=
  predecessor_excluded a [5,7,6,2,8,0] 1 0 4 5 (by decide) (by decide +kernel)

theorem node_1192 : Excluded a [5,7,6,2,8,1] :=
  source_excluded a [5,7,6,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1193 : Excluded a [5,7,6,2,8,3] :=
  source_excluded a [5,7,6,2,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1196 : Excluded a [5,7,6,2,8,4,0,1] :=
  predecessor_excluded a [5,7,6,2,8,4,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_1197 : Excluded a [5,7,6,2,8,4,0,3] :=
  predecessor_excluded a [5,7,6,2,8,4,0,3] 0 3 1 7 (by decide) (by decide +kernel)

theorem node_1195 : Excluded a [5,7,6,2,8,4,0] :=
  branch_excluded a [5,7,6,2,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,6,2,8,4,0,0] (by decide +kernel))
      node_1196
      (invalid_excluded a [5,7,6,2,8,4,0,2] (by decide +kernel))
      node_1197
      (invalid_excluded a [5,7,6,2,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,0,8] (by decide +kernel)))

theorem node_1198 : Excluded a [5,7,6,2,8,4,1] :=
  source_excluded a [5,7,6,2,8,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1199 : Excluded a [5,7,6,2,8,4,3] :=
  source_excluded a [5,7,6,2,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1194 : Excluded a [5,7,6,2,8,4] :=
  branch_excluded a [5,7,6,2,8,4] (by decide)
    (fin9_cases _
      node_1195
      node_1198
      (invalid_excluded a [5,7,6,2,8,4,2] (by decide +kernel))
      node_1199
      (invalid_excluded a [5,7,6,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,8] (by decide +kernel)))

theorem node_1190 : Excluded a [5,7,6,2,8] :=
  branch_excluded a [5,7,6,2,8] (by decide)
    (fin9_cases _
      node_1191
      node_1192
      (invalid_excluded a [5,7,6,2,8,2] (by decide +kernel))
      node_1193
      node_1194
      (invalid_excluded a [5,7,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,8] (by decide +kernel)))

theorem node_1186 : Excluded a [5,7,6,2] :=
  branch_excluded a [5,7,6,2] (by decide)
    (fin9_cases _
      node_1187
      node_1188
      (invalid_excluded a [5,7,6,2,2] (by decide +kernel))
      node_1189
      (invalid_excluded a [5,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,7] (by decide +kernel))
      node_1190)

theorem node_1201 : Excluded a [5,7,6,8,0] :=
  source_excluded a [5,7,6,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1202 : Excluded a [5,7,6,8,1] :=
  source_excluded a [5,7,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1203 : Excluded a [5,7,6,8,2] :=
  predecessor_excluded a [5,7,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_1206 : Excluded a [5,7,6,8,3,0,1] :=
  source_excluded a [5,7,6,8,3,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1207 : Excluded a [5,7,6,8,3,0,2] :=
  source_excluded a [5,7,6,8,3,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_1208 : Excluded a [5,7,6,8,3,0,4] :=
  predecessor_excluded a [5,7,6,8,3,0,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_1205 : Excluded a [5,7,6,8,3,0] :=
  branch_excluded a [5,7,6,8,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,6,8,3,0,0] (by decide +kernel))
      node_1206
      node_1207
      (invalid_excluded a [5,7,6,8,3,0,3] (by decide +kernel))
      node_1208
      (invalid_excluded a [5,7,6,8,3,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,3,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,3,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,3,0,8] (by decide +kernel)))

theorem node_1209 : Excluded a [5,7,6,8,3,1] :=
  source_excluded a [5,7,6,8,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1210 : Excluded a [5,7,6,8,3,2] :=
  source_excluded a [5,7,6,8,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1211 : Excluded a [5,7,6,8,3,4] :=
  predecessor_excluded a [5,7,6,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1204 : Excluded a [5,7,6,8,3] :=
  branch_excluded a [5,7,6,8,3] (by decide)
    (fin9_cases _
      node_1205
      node_1209
      node_1210
      (invalid_excluded a [5,7,6,8,3,3] (by decide +kernel))
      node_1211
      (invalid_excluded a [5,7,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,3,8] (by decide +kernel)))

theorem node_1200 : Excluded a [5,7,6,8] :=
  branch_excluded a [5,7,6,8] (by decide)
    (fin9_cases _
      node_1201
      node_1202
      node_1203
      node_1204
      (invalid_excluded a [5,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,8] (by decide +kernel)))

theorem node_1160 : Excluded a [5,7,6] :=
  branch_excluded a [5,7,6] (by decide)
    (fin9_cases _
      node_1161
      node_1162
      node_1186
      (invalid_excluded a [5,7,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,7] (by decide +kernel))
      node_1200)

theorem node_1212 : Excluded a [5,7,8] :=
  predecessor_excluded a [5,7,8] 0 8 1 2 (by decide) (by decide +kernel)

theorem node_1058 : Excluded a [5,7] :=
  branch_excluded a [5,7] (by decide)
    (fin9_cases _
      node_1059
      node_1109
      (invalid_excluded a [5,7,2] (by decide +kernel))
      (invalid_excluded a [5,7,3] (by decide +kernel))
      node_1159
      (invalid_excluded a [5,7,5] (by decide +kernel))
      node_1160
      (invalid_excluded a [5,7,7] (by decide +kernel))
      node_1212)

theorem node_1214 : Excluded a [5,8,0] :=
  predecessor_excluded a [5,8,0] 3 0 1 2 (by decide) (by decide +kernel)

theorem node_1216 : Excluded a [5,8,1,0] :=
  predecessor_excluded a [5,8,1,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1217 : Excluded a [5,8,1,2] :=
  predecessor_excluded a [5,8,1,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_1219 : Excluded a [5,8,1,6,0] :=
  source_excluded a [5,8,1,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1223 : Excluded a [5,8,1,6,2,0,3,4] :=
  predecessor_excluded a [5,8,1,6,2,0,3,4] 0 4 6 7 (by decide) (by decide +kernel)

theorem node_1222 : Excluded a [5,8,1,6,2,0,3] :=
  branch_excluded a [5,8,1,6,2,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,6,2,0,3,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,0,3,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,0,3,2] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,0,3,3] (by decide +kernel))
      node_1223
      (invalid_excluded a [5,8,1,6,2,0,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,0,3,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,0,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,0,3,8] (by decide +kernel)))

theorem node_1224 : Excluded a [5,8,1,6,2,0,4] :=
  source_excluded a [5,8,1,6,2,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1221 : Excluded a [5,8,1,6,2,0] :=
  branch_excluded a [5,8,1,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,6,2,0,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,0,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,0,2] (by decide +kernel))
      node_1222
      node_1224
      (invalid_excluded a [5,8,1,6,2,0,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,0,8] (by decide +kernel)))

theorem node_1225 : Excluded a [5,8,1,6,2,3] :=
  source_excluded a [5,8,1,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1226 : Excluded a [5,8,1,6,2,4] :=
  source_excluded a [5,8,1,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1227 : Excluded a [5,8,1,6,2,7] :=
  source_excluded a [5,8,1,6,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1220 : Excluded a [5,8,1,6,2] :=
  branch_excluded a [5,8,1,6,2] (by decide)
    (fin9_cases _
      node_1221
      (invalid_excluded a [5,8,1,6,2,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,2] (by decide +kernel))
      node_1225
      node_1226
      (invalid_excluded a [5,8,1,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,6] (by decide +kernel))
      node_1227
      (invalid_excluded a [5,8,1,6,2,8] (by decide +kernel)))

theorem node_1228 : Excluded a [5,8,1,6,3] :=
  predecessor_excluded a [5,8,1,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1229 : Excluded a [5,8,1,6,7] :=
  predecessor_excluded a [5,8,1,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1218 : Excluded a [5,8,1,6] :=
  branch_excluded a [5,8,1,6] (by decide)
    (fin9_cases _
      node_1219
      (invalid_excluded a [5,8,1,6,1] (by decide +kernel))
      node_1220
      node_1228
      (invalid_excluded a [5,8,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,6] (by decide +kernel))
      node_1229
      (invalid_excluded a [5,8,1,6,8] (by decide +kernel)))

theorem node_1231 : Excluded a [5,8,1,7,0] :=
  source_excluded a [5,8,1,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1234 : Excluded a [5,8,1,7,2,0,3] :=
  source_excluded a [5,8,1,7,2,0,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1235 : Excluded a [5,8,1,7,2,0,4] :=
  source_excluded a [5,8,1,7,2,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1233 : Excluded a [5,8,1,7,2,0] :=
  branch_excluded a [5,8,1,7,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,7,2,0,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,0,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,0,2] (by decide +kernel))
      node_1234
      node_1235
      (invalid_excluded a [5,8,1,7,2,0,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,0,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,0,8] (by decide +kernel)))

theorem node_1236 : Excluded a [5,8,1,7,2,3] :=
  predecessor_excluded a [5,8,1,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1240 : Excluded a [5,8,1,7,2,4,0,3,6] :=
  source_excluded a [5,8,1,7,2,4,0,3,6] 8 1 6 (by decide) (by decide +kernel)

theorem node_1239 : Excluded a [5,8,1,7,2,4,0,3] :=
  branch_excluded a [5,8,1,7,2,4,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,7,2,4,0,3,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,3,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,3,2] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,3,3] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,3,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,3,5] (by decide +kernel))
      node_1240
      (invalid_excluded a [5,8,1,7,2,4,0,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,3,8] (by decide +kernel)))

theorem node_1241 : Excluded a [5,8,1,7,2,4,0,6] :=
  predecessor_excluded a [5,8,1,7,2,4,0,6] 1 0 7 6 (by decide) (by decide +kernel)

theorem node_1238 : Excluded a [5,8,1,7,2,4,0] :=
  branch_excluded a [5,8,1,7,2,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,7,2,4,0,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,2] (by decide +kernel))
      node_1239
      (invalid_excluded a [5,8,1,7,2,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,5] (by decide +kernel))
      node_1241
      (invalid_excluded a [5,8,1,7,2,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,8] (by decide +kernel)))

theorem node_1242 : Excluded a [5,8,1,7,2,4,3] :=
  source_excluded a [5,8,1,7,2,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1237 : Excluded a [5,8,1,7,2,4] :=
  branch_excluded a [5,8,1,7,2,4] (by decide)
    (fin9_cases _
      node_1238
      (invalid_excluded a [5,8,1,7,2,4,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,2] (by decide +kernel))
      node_1242
      (invalid_excluded a [5,8,1,7,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,8] (by decide +kernel)))

theorem node_1232 : Excluded a [5,8,1,7,2] :=
  branch_excluded a [5,8,1,7,2] (by decide)
    (fin9_cases _
      node_1233
      (invalid_excluded a [5,8,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,2] (by decide +kernel))
      node_1236
      node_1237
      (invalid_excluded a [5,8,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,8] (by decide +kernel)))

theorem node_1246 : Excluded a [5,8,1,7,3,0,2,4] :=
  source_excluded a [5,8,1,7,3,0,2,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_1248 : Excluded a [5,8,1,7,3,0,2,6,4] :=
  predecessor_excluded a [5,8,1,7,3,0,2,6,4] 1 5 8 0 (by decide) (by decide +kernel)

theorem node_1247 : Excluded a [5,8,1,7,3,0,2,6] :=
  branch_excluded a [5,8,1,7,3,0,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,7,3,0,2,6,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,0,2,6,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,0,2,6,2] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,0,2,6,3] (by decide +kernel))
      node_1248
      (invalid_excluded a [5,8,1,7,3,0,2,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,0,2,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,0,2,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,0,2,6,8] (by decide +kernel)))

theorem node_1245 : Excluded a [5,8,1,7,3,0,2] :=
  branch_excluded a [5,8,1,7,3,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,7,3,0,2,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,0,2,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,0,2,2] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,0,2,3] (by decide +kernel))
      node_1246
      (invalid_excluded a [5,8,1,7,3,0,2,5] (by decide +kernel))
      node_1247
      (invalid_excluded a [5,8,1,7,3,0,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,0,2,8] (by decide +kernel)))

theorem node_1249 : Excluded a [5,8,1,7,3,0,4] :=
  source_excluded a [5,8,1,7,3,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1244 : Excluded a [5,8,1,7,3,0] :=
  branch_excluded a [5,8,1,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,7,3,0,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,0,1] (by decide +kernel))
      node_1245
      (invalid_excluded a [5,8,1,7,3,0,3] (by decide +kernel))
      node_1249
      (invalid_excluded a [5,8,1,7,3,0,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,0,8] (by decide +kernel)))

theorem node_1250 : Excluded a [5,8,1,7,3,2] :=
  predecessor_excluded a [5,8,1,7,3,2] 3 2 0 5 (by decide) (by decide +kernel)

theorem node_1251 : Excluded a [5,8,1,7,3,4] :=
  predecessor_excluded a [5,8,1,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1243 : Excluded a [5,8,1,7,3] :=
  branch_excluded a [5,8,1,7,3] (by decide)
    (fin9_cases _
      node_1244
      (invalid_excluded a [5,8,1,7,3,1] (by decide +kernel))
      node_1250
      (invalid_excluded a [5,8,1,7,3,3] (by decide +kernel))
      node_1251
      (invalid_excluded a [5,8,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,8] (by decide +kernel)))

theorem node_1252 : Excluded a [5,8,1,7,6] :=
  source_excluded a [5,8,1,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1230 : Excluded a [5,8,1,7] :=
  branch_excluded a [5,8,1,7] (by decide)
    (fin9_cases _
      node_1231
      (invalid_excluded a [5,8,1,7,1] (by decide +kernel))
      node_1232
      node_1243
      (invalid_excluded a [5,8,1,7,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,5] (by decide +kernel))
      node_1252
      (invalid_excluded a [5,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,8] (by decide +kernel)))

theorem node_1215 : Excluded a [5,8,1] :=
  branch_excluded a [5,8,1] (by decide)
    (fin9_cases _
      node_1216
      (invalid_excluded a [5,8,1,1] (by decide +kernel))
      node_1217
      (invalid_excluded a [5,8,1,3] (by decide +kernel))
      (invalid_excluded a [5,8,1,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,5] (by decide +kernel))
      node_1218
      node_1230
      (invalid_excluded a [5,8,1,8] (by decide +kernel)))

theorem node_1253 : Excluded a [5,8,4] :=
  source_excluded a [5,8,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1255 : Excluded a [5,8,6,0] :=
  predecessor_excluded a [5,8,6,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1257 : Excluded a [5,8,6,1,0] :=
  source_excluded a [5,8,6,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1258 : Excluded a [5,8,6,1,2] :=
  predecessor_excluded a [5,8,6,1,2] 0 6 4 2 (by decide) (by decide +kernel)

def b_1263 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 8
  | 2 => 6
  | 3 => 1
  | 4 => 3
  | 5 => 0
  | 6 => 2
  | 7 => 4
  | 8 => 7
  | _ => 0

def cert_1263 : LosingRegion (edgeOf a b_1263) 0 :=
  losingMask a b_1263 0 1212475702085430714237952
    (by decide +kernel) (by decide +kernel)

theorem node_1263 : Excluded a [5,8,6,1,3,0,2,4,7] :=
  losing_excluded a [5,8,6,1,3,0,2,4,7] (by decide) b_1263 (by decide +kernel) 1 0 7 cert_1263 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_1263 1 0 ∧ 7 ≠ 1 ∧ maskRegion 1212475702085430714237952 1 7; decide +kernel)

theorem node_1262 : Excluded a [5,8,6,1,3,0,2,4] :=
  branch_excluded a [5,8,6,1,3,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,6,1,3,0,2,4,0] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,2,4,1] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,2,4,2] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,2,4,3] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,2,4,6] (by decide +kernel))
      node_1263
      (invalid_excluded a [5,8,6,1,3,0,2,4,8] (by decide +kernel)))

theorem node_1261 : Excluded a [5,8,6,1,3,0,2] :=
  branch_excluded a [5,8,6,1,3,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,6,1,3,0,2,0] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,2,1] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,2,2] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,2,3] (by decide +kernel))
      node_1262
      (invalid_excluded a [5,8,6,1,3,0,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,2,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,2,8] (by decide +kernel)))

theorem node_1264 : Excluded a [5,8,6,1,3,0,4] :=
  predecessor_excluded a [5,8,6,1,3,0,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_1260 : Excluded a [5,8,6,1,3,0] :=
  branch_excluded a [5,8,6,1,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,6,1,3,0,0] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,1] (by decide +kernel))
      node_1261
      (invalid_excluded a [5,8,6,1,3,0,3] (by decide +kernel))
      node_1264
      (invalid_excluded a [5,8,6,1,3,0,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,0,8] (by decide +kernel)))

theorem node_1265 : Excluded a [5,8,6,1,3,2] :=
  source_excluded a [5,8,6,1,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1266 : Excluded a [5,8,6,1,3,4] :=
  predecessor_excluded a [5,8,6,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1267 : Excluded a [5,8,6,1,3,7] :=
  source_excluded a [5,8,6,1,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1259 : Excluded a [5,8,6,1,3] :=
  branch_excluded a [5,8,6,1,3] (by decide)
    (fin9_cases _
      node_1260
      (invalid_excluded a [5,8,6,1,3,1] (by decide +kernel))
      node_1265
      (invalid_excluded a [5,8,6,1,3,3] (by decide +kernel))
      node_1266
      (invalid_excluded a [5,8,6,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,6] (by decide +kernel))
      node_1267
      (invalid_excluded a [5,8,6,1,3,8] (by decide +kernel)))

theorem node_1271 : Excluded a [5,8,6,1,7,0,2,3] :=
  predecessor_excluded a [5,8,6,1,7,0,2,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_1273 : Excluded a [5,8,6,1,7,0,2,4,3] :=
  predecessor_excluded a [5,8,6,1,7,0,2,4,3] 2 1 8 3 (by decide) (by decide +kernel)

theorem node_1272 : Excluded a [5,8,6,1,7,0,2,4] :=
  branch_excluded a [5,8,6,1,7,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,6,1,7,0,2,4,0] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,2,4,1] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,2,4,2] (by decide +kernel))
      node_1273
      (invalid_excluded a [5,8,6,1,7,0,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,2,4,8] (by decide +kernel)))

theorem node_1270 : Excluded a [5,8,6,1,7,0,2] :=
  branch_excluded a [5,8,6,1,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,6,1,7,0,2,0] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,2,1] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,2,2] (by decide +kernel))
      node_1271
      node_1272
      (invalid_excluded a [5,8,6,1,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,2,8] (by decide +kernel)))

theorem node_1274 : Excluded a [5,8,6,1,7,0,3] :=
  source_excluded a [5,8,6,1,7,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1275 : Excluded a [5,8,6,1,7,0,4] :=
  source_excluded a [5,8,6,1,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1269 : Excluded a [5,8,6,1,7,0] :=
  branch_excluded a [5,8,6,1,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,6,1,7,0,0] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,1] (by decide +kernel))
      node_1270
      node_1274
      node_1275
      (invalid_excluded a [5,8,6,1,7,0,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,0,8] (by decide +kernel)))

theorem node_1276 : Excluded a [5,8,6,1,7,2] :=
  source_excluded a [5,8,6,1,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1277 : Excluded a [5,8,6,1,7,3] :=
  source_excluded a [5,8,6,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1278 : Excluded a [5,8,6,1,7,4] :=
  predecessor_excluded a [5,8,6,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1268 : Excluded a [5,8,6,1,7] :=
  branch_excluded a [5,8,6,1,7] (by decide)
    (fin9_cases _
      node_1269
      (invalid_excluded a [5,8,6,1,7,1] (by decide +kernel))
      node_1276
      node_1277
      node_1278
      (invalid_excluded a [5,8,6,1,7,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,8] (by decide +kernel)))

theorem node_1256 : Excluded a [5,8,6,1] :=
  branch_excluded a [5,8,6,1] (by decide)
    (fin9_cases _
      node_1257
      (invalid_excluded a [5,8,6,1,1] (by decide +kernel))
      node_1258
      node_1259
      (invalid_excluded a [5,8,6,1,4] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,6] (by decide +kernel))
      node_1268
      (invalid_excluded a [5,8,6,1,8] (by decide +kernel)))

theorem node_1280 : Excluded a [5,8,6,2,0] :=
  source_excluded a [5,8,6,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1281 : Excluded a [5,8,6,2,1] :=
  source_excluded a [5,8,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1282 : Excluded a [5,8,6,2,3] :=
  predecessor_excluded a [5,8,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1285 : Excluded a [5,8,6,2,7,0,1] :=
  predecessor_excluded a [5,8,6,2,7,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_1286 : Excluded a [5,8,6,2,7,0,3] :=
  source_excluded a [5,8,6,2,7,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1287 : Excluded a [5,8,6,2,7,0,4] :=
  source_excluded a [5,8,6,2,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1284 : Excluded a [5,8,6,2,7,0] :=
  branch_excluded a [5,8,6,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,6,2,7,0,0] (by decide +kernel))
      node_1285
      (invalid_excluded a [5,8,6,2,7,0,2] (by decide +kernel))
      node_1286
      node_1287
      (invalid_excluded a [5,8,6,2,7,0,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,0,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,0,8] (by decide +kernel)))

theorem node_1288 : Excluded a [5,8,6,2,7,1] :=
  source_excluded a [5,8,6,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1289 : Excluded a [5,8,6,2,7,3] :=
  source_excluded a [5,8,6,2,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1290 : Excluded a [5,8,6,2,7,4] :=
  predecessor_excluded a [5,8,6,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1283 : Excluded a [5,8,6,2,7] :=
  branch_excluded a [5,8,6,2,7] (by decide)
    (fin9_cases _
      node_1284
      node_1288
      (invalid_excluded a [5,8,6,2,7,2] (by decide +kernel))
      node_1289
      node_1290
      (invalid_excluded a [5,8,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,8] (by decide +kernel)))

theorem node_1279 : Excluded a [5,8,6,2] :=
  branch_excluded a [5,8,6,2] (by decide)
    (fin9_cases _
      node_1280
      node_1281
      (invalid_excluded a [5,8,6,2,2] (by decide +kernel))
      node_1282
      (invalid_excluded a [5,8,6,2,4] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,6] (by decide +kernel))
      node_1283
      (invalid_excluded a [5,8,6,2,8] (by decide +kernel)))

theorem node_1291 : Excluded a [5,8,6,7] :=
  predecessor_excluded a [5,8,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_1254 : Excluded a [5,8,6] :=
  branch_excluded a [5,8,6] (by decide)
    (fin9_cases _
      node_1255
      node_1256
      node_1279
      (invalid_excluded a [5,8,6,3] (by decide +kernel))
      (invalid_excluded a [5,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,6] (by decide +kernel))
      node_1291
      (invalid_excluded a [5,8,6,8] (by decide +kernel)))

theorem node_1293 : Excluded a [5,8,7,0] :=
  predecessor_excluded a [5,8,7,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1295 : Excluded a [5,8,7,1,0] :=
  source_excluded a [5,8,7,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1296 : Excluded a [5,8,7,1,2] :=
  predecessor_excluded a [5,8,7,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1299 : Excluded a [5,8,7,1,3,0,2] :=
  source_excluded a [5,8,7,1,3,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1301 : Excluded a [5,8,7,1,3,0,4,2] :=
  source_excluded a [5,8,7,1,3,0,4,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_1303 : Excluded a [5,8,7,1,3,0,4,6,2] :=
  source_excluded a [5,8,7,1,3,0,4,6,2] 1 0 8 (by decide) (by decide +kernel)

theorem node_1302 : Excluded a [5,8,7,1,3,0,4,6] :=
  branch_excluded a [5,8,7,1,3,0,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,1,3,0,4,6,0] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,6,1] (by decide +kernel))
      node_1303
      (invalid_excluded a [5,8,7,1,3,0,4,6,3] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,6,8] (by decide +kernel)))

theorem node_1300 : Excluded a [5,8,7,1,3,0,4] :=
  branch_excluded a [5,8,7,1,3,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,1,3,0,4,0] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,1] (by decide +kernel))
      node_1301
      (invalid_excluded a [5,8,7,1,3,0,4,3] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,5] (by decide +kernel))
      node_1302
      (invalid_excluded a [5,8,7,1,3,0,4,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,4,8] (by decide +kernel)))

theorem node_1298 : Excluded a [5,8,7,1,3,0] :=
  branch_excluded a [5,8,7,1,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,1,3,0,0] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,1] (by decide +kernel))
      node_1299
      (invalid_excluded a [5,8,7,1,3,0,3] (by decide +kernel))
      node_1300
      (invalid_excluded a [5,8,7,1,3,0,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,0,8] (by decide +kernel)))

theorem node_1304 : Excluded a [5,8,7,1,3,2] :=
  predecessor_excluded a [5,8,7,1,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1305 : Excluded a [5,8,7,1,3,4] :=
  predecessor_excluded a [5,8,7,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1297 : Excluded a [5,8,7,1,3] :=
  branch_excluded a [5,8,7,1,3] (by decide)
    (fin9_cases _
      node_1298
      (invalid_excluded a [5,8,7,1,3,1] (by decide +kernel))
      node_1304
      (invalid_excluded a [5,8,7,1,3,3] (by decide +kernel))
      node_1305
      (invalid_excluded a [5,8,7,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,8] (by decide +kernel)))

theorem node_1306 : Excluded a [5,8,7,1,6] :=
  source_excluded a [5,8,7,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1294 : Excluded a [5,8,7,1] :=
  branch_excluded a [5,8,7,1] (by decide)
    (fin9_cases _
      node_1295
      (invalid_excluded a [5,8,7,1,1] (by decide +kernel))
      node_1296
      node_1297
      (invalid_excluded a [5,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,5] (by decide +kernel))
      node_1306
      (invalid_excluded a [5,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,8] (by decide +kernel)))

theorem node_1308 : Excluded a [5,8,7,2,0] :=
  source_excluded a [5,8,7,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1309 : Excluded a [5,8,7,2,1] :=
  source_excluded a [5,8,7,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1310 : Excluded a [5,8,7,2,3] :=
  predecessor_excluded a [5,8,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1311 : Excluded a [5,8,7,2,6] :=
  source_excluded a [5,8,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1307 : Excluded a [5,8,7,2] :=
  branch_excluded a [5,8,7,2] (by decide)
    (fin9_cases _
      node_1308
      node_1309
      (invalid_excluded a [5,8,7,2,2] (by decide +kernel))
      node_1310
      (invalid_excluded a [5,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,5] (by decide +kernel))
      node_1311
      (invalid_excluded a [5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,8] (by decide +kernel)))

theorem node_1313 : Excluded a [5,8,7,6,0] :=
  source_excluded a [5,8,7,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1314 : Excluded a [5,8,7,6,1] :=
  source_excluded a [5,8,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1317 : Excluded a [5,8,7,6,2,0,1] :=
  predecessor_excluded a [5,8,7,6,2,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_1318 : Excluded a [5,8,7,6,2,0,3] :=
  source_excluded a [5,8,7,6,2,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1319 : Excluded a [5,8,7,6,2,0,4] :=
  source_excluded a [5,8,7,6,2,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1316 : Excluded a [5,8,7,6,2,0] :=
  branch_excluded a [5,8,7,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,6,2,0,0] (by decide +kernel))
      node_1317
      (invalid_excluded a [5,8,7,6,2,0,2] (by decide +kernel))
      node_1318
      node_1319
      (invalid_excluded a [5,8,7,6,2,0,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,0,8] (by decide +kernel)))

theorem node_1320 : Excluded a [5,8,7,6,2,1] :=
  source_excluded a [5,8,7,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1321 : Excluded a [5,8,7,6,2,3] :=
  source_excluded a [5,8,7,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1322 : Excluded a [5,8,7,6,2,4] :=
  source_excluded a [5,8,7,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1315 : Excluded a [5,8,7,6,2] :=
  branch_excluded a [5,8,7,6,2] (by decide)
    (fin9_cases _
      node_1316
      node_1320
      (invalid_excluded a [5,8,7,6,2,2] (by decide +kernel))
      node_1321
      node_1322
      (invalid_excluded a [5,8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,8] (by decide +kernel)))

theorem node_1323 : Excluded a [5,8,7,6,3] :=
  predecessor_excluded a [5,8,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1312 : Excluded a [5,8,7,6] :=
  branch_excluded a [5,8,7,6] (by decide)
    (fin9_cases _
      node_1313
      node_1314
      node_1315
      node_1323
      (invalid_excluded a [5,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,8] (by decide +kernel)))

theorem node_1292 : Excluded a [5,8,7] :=
  branch_excluded a [5,8,7] (by decide)
    (fin9_cases _
      node_1293
      node_1294
      node_1307
      (invalid_excluded a [5,8,7,3] (by decide +kernel))
      (invalid_excluded a [5,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,5] (by decide +kernel))
      node_1312
      (invalid_excluded a [5,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,8] (by decide +kernel)))

theorem node_1213 : Excluded a [5,8] :=
  branch_excluded a [5,8] (by decide)
    (fin9_cases _
      node_1214
      node_1215
      (invalid_excluded a [5,8,2] (by decide +kernel))
      (invalid_excluded a [5,8,3] (by decide +kernel))
      node_1253
      (invalid_excluded a [5,8,5] (by decide +kernel))
      node_1254
      node_1292
      (invalid_excluded a [5,8,8] (by decide +kernel)))

theorem node_797 : Excluded a [5] :=
  branch_excluded a [5] (by decide)
    (fin9_cases _
      node_798
      (invalid_excluded a [5,1] (by decide +kernel))
      (invalid_excluded a [5,2] (by decide +kernel))
      node_967
      node_968
      (invalid_excluded a [5,5] (by decide +kernel))
      node_1057
      node_1058
      node_1213)

theorem node_1326 : Excluded a [6,0,1] :=
  predecessor_excluded a [6,0,1] 3 1 1 2 (by decide) (by decide +kernel)

theorem node_1327 : Excluded a [6,0,4] :=
  source_excluded a [6,0,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1330 : Excluded a [6,0,5,1,2] :=
  source_excluded a [6,0,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1331 : Excluded a [6,0,5,1,3] :=
  source_excluded a [6,0,5,1,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1334 : Excluded a [6,0,5,1,7,2,3] :=
  predecessor_excluded a [6,0,5,1,7,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_1335 : Excluded a [6,0,5,1,7,2,4] :=
  source_excluded a [6,0,5,1,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1336 : Excluded a [6,0,5,1,7,2,8] :=
  source_excluded a [6,0,5,1,7,2,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_1333 : Excluded a [6,0,5,1,7,2] :=
  branch_excluded a [6,0,5,1,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,5,1,7,2,0] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,7,2,2] (by decide +kernel))
      node_1334
      node_1335
      (invalid_excluded a [6,0,5,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,7,2,7] (by decide +kernel))
      node_1336)

theorem node_1337 : Excluded a [6,0,5,1,7,3] :=
  source_excluded a [6,0,5,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1338 : Excluded a [6,0,5,1,7,4] :=
  predecessor_excluded a [6,0,5,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1339 : Excluded a [6,0,5,1,7,8] :=
  predecessor_excluded a [6,0,5,1,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_1332 : Excluded a [6,0,5,1,7] :=
  branch_excluded a [6,0,5,1,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,5,1,7,0] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,7,1] (by decide +kernel))
      node_1333
      node_1337
      node_1338
      (invalid_excluded a [6,0,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,7,7] (by decide +kernel))
      node_1339)

theorem node_1342 : Excluded a [6,0,5,1,8,2,3] :=
  predecessor_excluded a [6,0,5,1,8,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_1343 : Excluded a [6,0,5,1,8,2,4] :=
  predecessor_excluded a [6,0,5,1,8,2,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1341 : Excluded a [6,0,5,1,8,2] :=
  branch_excluded a [6,0,5,1,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,5,1,8,2,0] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,8,2,1] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,8,2,2] (by decide +kernel))
      node_1342
      node_1343
      (invalid_excluded a [6,0,5,1,8,2,5] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,8,2,6] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,8,2,7] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,8,2,8] (by decide +kernel)))

theorem node_1344 : Excluded a [6,0,5,1,8,3] :=
  source_excluded a [6,0,5,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1345 : Excluded a [6,0,5,1,8,4] :=
  predecessor_excluded a [6,0,5,1,8,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_1346 : Excluded a [6,0,5,1,8,7] :=
  source_excluded a [6,0,5,1,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1340 : Excluded a [6,0,5,1,8] :=
  branch_excluded a [6,0,5,1,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,5,1,8,0] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,8,1] (by decide +kernel))
      node_1341
      node_1344
      node_1345
      (invalid_excluded a [6,0,5,1,8,5] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,8,6] (by decide +kernel))
      node_1346
      (invalid_excluded a [6,0,5,1,8,8] (by decide +kernel)))

theorem node_1329 : Excluded a [6,0,5,1] :=
  branch_excluded a [6,0,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,5,1,0] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,1] (by decide +kernel))
      node_1330
      node_1331
      (invalid_excluded a [6,0,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,0,5,1,6] (by decide +kernel))
      node_1332
      node_1340)

theorem node_1347 : Excluded a [6,0,5,2] :=
  predecessor_excluded a [6,0,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_1350 : Excluded a [6,0,5,7,1,2] :=
  predecessor_excluded a [6,0,5,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1351 : Excluded a [6,0,5,7,1,3] :=
  source_excluded a [6,0,5,7,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1352 : Excluded a [6,0,5,7,1,4] :=
  predecessor_excluded a [6,0,5,7,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_1354 : Excluded a [6,0,5,7,1,8,2] :=
  predecessor_excluded a [6,0,5,7,1,8,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1355 : Excluded a [6,0,5,7,1,8,3] :=
  source_excluded a [6,0,5,7,1,8,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1356 : Excluded a [6,0,5,7,1,8,4] :=
  source_excluded a [6,0,5,7,1,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1353 : Excluded a [6,0,5,7,1,8] :=
  branch_excluded a [6,0,5,7,1,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,5,7,1,8,0] (by decide +kernel))
      (invalid_excluded a [6,0,5,7,1,8,1] (by decide +kernel))
      node_1354
      node_1355
      node_1356
      (invalid_excluded a [6,0,5,7,1,8,5] (by decide +kernel))
      (invalid_excluded a [6,0,5,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [6,0,5,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [6,0,5,7,1,8,8] (by decide +kernel)))

theorem node_1349 : Excluded a [6,0,5,7,1] :=
  branch_excluded a [6,0,5,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,5,7,1,0] (by decide +kernel))
      (invalid_excluded a [6,0,5,7,1,1] (by decide +kernel))
      node_1350
      node_1351
      node_1352
      (invalid_excluded a [6,0,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,0,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,0,5,7,1,7] (by decide +kernel))
      node_1353)

theorem node_1357 : Excluded a [6,0,5,7,2] :=
  source_excluded a [6,0,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1358 : Excluded a [6,0,5,7,3] :=
  source_excluded a [6,0,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1359 : Excluded a [6,0,5,7,8] :=
  predecessor_excluded a [6,0,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1348 : Excluded a [6,0,5,7] :=
  branch_excluded a [6,0,5,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,5,7,0] (by decide +kernel))
      node_1349
      node_1357
      node_1358
      (invalid_excluded a [6,0,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,0,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,0,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,0,5,7,7] (by decide +kernel))
      node_1359)

theorem node_1362 : Excluded a [6,0,5,8,1,2] :=
  predecessor_excluded a [6,0,5,8,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1363 : Excluded a [6,0,5,8,1,3] :=
  source_excluded a [6,0,5,8,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1364 : Excluded a [6,0,5,8,1,4] :=
  predecessor_excluded a [6,0,5,8,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_1365 : Excluded a [6,0,5,8,1,7] :=
  source_excluded a [6,0,5,8,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1361 : Excluded a [6,0,5,8,1] :=
  branch_excluded a [6,0,5,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,5,8,1,0] (by decide +kernel))
      (invalid_excluded a [6,0,5,8,1,1] (by decide +kernel))
      node_1362
      node_1363
      node_1364
      (invalid_excluded a [6,0,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [6,0,5,8,1,6] (by decide +kernel))
      node_1365
      (invalid_excluded a [6,0,5,8,1,8] (by decide +kernel)))

theorem node_1366 : Excluded a [6,0,5,8,2] :=
  source_excluded a [6,0,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1367 : Excluded a [6,0,5,8,3] :=
  source_excluded a [6,0,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1369 : Excluded a [6,0,5,8,7,1] :=
  source_excluded a [6,0,5,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1371 : Excluded a [6,0,5,8,7,2,1] :=
  source_excluded a [6,0,5,8,7,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1372 : Excluded a [6,0,5,8,7,2,3] :=
  predecessor_excluded a [6,0,5,8,7,2,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_1373 : Excluded a [6,0,5,8,7,2,4] :=
  source_excluded a [6,0,5,8,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1370 : Excluded a [6,0,5,8,7,2] :=
  branch_excluded a [6,0,5,8,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,5,8,7,2,0] (by decide +kernel))
      node_1371
      (invalid_excluded a [6,0,5,8,7,2,2] (by decide +kernel))
      node_1372
      node_1373
      (invalid_excluded a [6,0,5,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,0,5,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,0,5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,0,5,8,7,2,8] (by decide +kernel)))

theorem node_1374 : Excluded a [6,0,5,8,7,3] :=
  source_excluded a [6,0,5,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1375 : Excluded a [6,0,5,8,7,4] :=
  predecessor_excluded a [6,0,5,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1368 : Excluded a [6,0,5,8,7] :=
  branch_excluded a [6,0,5,8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,5,8,7,0] (by decide +kernel))
      node_1369
      node_1370
      node_1374
      node_1375
      (invalid_excluded a [6,0,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,0,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,0,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,0,5,8,7,8] (by decide +kernel)))

theorem node_1360 : Excluded a [6,0,5,8] :=
  branch_excluded a [6,0,5,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,5,8,0] (by decide +kernel))
      node_1361
      node_1366
      node_1367
      (invalid_excluded a [6,0,5,8,4] (by decide +kernel))
      (invalid_excluded a [6,0,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,0,5,8,6] (by decide +kernel))
      node_1368
      (invalid_excluded a [6,0,5,8,8] (by decide +kernel)))

theorem node_1328 : Excluded a [6,0,5] :=
  branch_excluded a [6,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,5,0] (by decide +kernel))
      node_1329
      node_1347
      (invalid_excluded a [6,0,5,3] (by decide +kernel))
      (invalid_excluded a [6,0,5,4] (by decide +kernel))
      (invalid_excluded a [6,0,5,5] (by decide +kernel))
      (invalid_excluded a [6,0,5,6] (by decide +kernel))
      node_1348
      node_1360)

theorem node_1378 : Excluded a [6,0,7,1,2] :=
  predecessor_excluded a [6,0,7,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1380 : Excluded a [6,0,7,1,3,2] :=
  predecessor_excluded a [6,0,7,1,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1381 : Excluded a [6,0,7,1,3,4] :=
  predecessor_excluded a [6,0,7,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1383 : Excluded a [6,0,7,1,3,8,2] :=
  source_excluded a [6,0,7,1,3,8,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1386 : Excluded a [6,0,7,1,3,8,4,2,5] :=
  predecessor_excluded a [6,0,7,1,3,8,4,2,5] 1 6 8 0 (by decide) (by decide +kernel)

theorem node_1385 : Excluded a [6,0,7,1,3,8,4,2] :=
  branch_excluded a [6,0,7,1,3,8,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,1,3,8,4,2,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,8,4,2,1] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,8,4,2,2] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,8,4,2,3] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,8,4,2,4] (by decide +kernel))
      node_1386
      (invalid_excluded a [6,0,7,1,3,8,4,2,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,8,4,2,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,8,4,2,8] (by decide +kernel)))

theorem node_1387 : Excluded a [6,0,7,1,3,8,4,5] :=
  source_excluded a [6,0,7,1,3,8,4,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_1384 : Excluded a [6,0,7,1,3,8,4] :=
  branch_excluded a [6,0,7,1,3,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,1,3,8,4,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,8,4,1] (by decide +kernel))
      node_1385
      (invalid_excluded a [6,0,7,1,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,8,4,4] (by decide +kernel))
      node_1387
      (invalid_excluded a [6,0,7,1,3,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,8,4,8] (by decide +kernel)))

theorem node_1388 : Excluded a [6,0,7,1,3,8,5] :=
  predecessor_excluded a [6,0,7,1,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_1382 : Excluded a [6,0,7,1,3,8] :=
  branch_excluded a [6,0,7,1,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,1,3,8,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,8,1] (by decide +kernel))
      node_1383
      (invalid_excluded a [6,0,7,1,3,8,3] (by decide +kernel))
      node_1384
      node_1388
      (invalid_excluded a [6,0,7,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,8,8] (by decide +kernel)))

theorem node_1379 : Excluded a [6,0,7,1,3] :=
  branch_excluded a [6,0,7,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,1,3,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,1] (by decide +kernel))
      node_1380
      (invalid_excluded a [6,0,7,1,3,3] (by decide +kernel))
      node_1381
      (invalid_excluded a [6,0,7,1,3,5] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,3,7] (by decide +kernel))
      node_1382)

theorem node_1390 : Excluded a [6,0,7,1,8,2] :=
  predecessor_excluded a [6,0,7,1,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1392 : Excluded a [6,0,7,1,8,3,2] :=
  source_excluded a [6,0,7,1,8,3,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1393 : Excluded a [6,0,7,1,8,3,4] :=
  predecessor_excluded a [6,0,7,1,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

def b_1396 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 0
  | 2 => 7
  | 3 => 1
  | 4 => 8
  | 5 => 3
  | 6 => 5
  | 7 => 2
  | 8 => 4
  | _ => 0

def cert_1396 : LosingRegion (edgeOf a b_1396) 0 :=
  losingMask a b_1396 0 1210109943333988519117824
    (by decide +kernel) (by decide +kernel)

theorem node_1396 : Excluded a [6,0,7,1,8,3,5,2,4] :=
  losing_excluded a [6,0,7,1,8,3,5,2,4] (by decide) b_1396 (by decide +kernel) 4 0 7 cert_1396 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_1396 4 0 ∧ 7 ≠ 4 ∧ maskRegion 1210109943333988519117824 4 7; decide +kernel)

theorem node_1395 : Excluded a [6,0,7,1,8,3,5,2] :=
  branch_excluded a [6,0,7,1,8,3,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,1,8,3,5,2,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,3,5,2,1] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,3,5,2,2] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,3,5,2,3] (by decide +kernel))
      node_1396
      (invalid_excluded a [6,0,7,1,8,3,5,2,5] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,3,5,2,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,3,5,2,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,3,5,2,8] (by decide +kernel)))

theorem node_1397 : Excluded a [6,0,7,1,8,3,5,4] :=
  source_excluded a [6,0,7,1,8,3,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_1394 : Excluded a [6,0,7,1,8,3,5] :=
  branch_excluded a [6,0,7,1,8,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,1,8,3,5,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,3,5,1] (by decide +kernel))
      node_1395
      (invalid_excluded a [6,0,7,1,8,3,5,3] (by decide +kernel))
      node_1397
      (invalid_excluded a [6,0,7,1,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,3,5,8] (by decide +kernel)))

theorem node_1391 : Excluded a [6,0,7,1,8,3] :=
  branch_excluded a [6,0,7,1,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,1,8,3,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,3,1] (by decide +kernel))
      node_1392
      (invalid_excluded a [6,0,7,1,8,3,3] (by decide +kernel))
      node_1393
      node_1394
      (invalid_excluded a [6,0,7,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,3,8] (by decide +kernel)))

theorem node_1399 : Excluded a [6,0,7,1,8,4,2] :=
  source_excluded a [6,0,7,1,8,4,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1400 : Excluded a [6,0,7,1,8,4,3] :=
  source_excluded a [6,0,7,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1401 : Excluded a [6,0,7,1,8,4,5] :=
  predecessor_excluded a [6,0,7,1,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1398 : Excluded a [6,0,7,1,8,4] :=
  branch_excluded a [6,0,7,1,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,1,8,4,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,4,1] (by decide +kernel))
      node_1399
      node_1400
      (invalid_excluded a [6,0,7,1,8,4,4] (by decide +kernel))
      node_1401
      (invalid_excluded a [6,0,7,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,4,8] (by decide +kernel)))

theorem node_1389 : Excluded a [6,0,7,1,8] :=
  branch_excluded a [6,0,7,1,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,1,8,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,1] (by decide +kernel))
      node_1390
      node_1391
      node_1398
      (invalid_excluded a [6,0,7,1,8,5] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,8,8] (by decide +kernel)))

theorem node_1377 : Excluded a [6,0,7,1] :=
  branch_excluded a [6,0,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,1,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,1] (by decide +kernel))
      node_1378
      node_1379
      (invalid_excluded a [6,0,7,1,4] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,1,7] (by decide +kernel))
      node_1389)

theorem node_1405 : Excluded a [6,0,7,2,1,3,4] :=
  predecessor_excluded a [6,0,7,2,1,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_1407 : Excluded a [6,0,7,2,1,3,5,4] :=
  predecessor_excluded a [6,0,7,2,1,3,5,4] 0 4 2 7 (by decide) (by decide +kernel)

theorem node_1406 : Excluded a [6,0,7,2,1,3,5] :=
  branch_excluded a [6,0,7,2,1,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,2,1,3,5,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,3,5,3] (by decide +kernel))
      node_1407
      (invalid_excluded a [6,0,7,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,3,5,8] (by decide +kernel)))

theorem node_1408 : Excluded a [6,0,7,2,1,3,8] :=
  source_excluded a [6,0,7,2,1,3,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_1404 : Excluded a [6,0,7,2,1,3] :=
  branch_excluded a [6,0,7,2,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,2,1,3,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,3,3] (by decide +kernel))
      node_1405
      node_1406
      (invalid_excluded a [6,0,7,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,3,7] (by decide +kernel))
      node_1408)

theorem node_1410 : Excluded a [6,0,7,2,1,4,3] :=
  source_excluded a [6,0,7,2,1,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1411 : Excluded a [6,0,7,2,1,4,5] :=
  predecessor_excluded a [6,0,7,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1412 : Excluded a [6,0,7,2,1,4,8] :=
  source_excluded a [6,0,7,2,1,4,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_1409 : Excluded a [6,0,7,2,1,4] :=
  branch_excluded a [6,0,7,2,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,2,1,4,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,4,2] (by decide +kernel))
      node_1410
      (invalid_excluded a [6,0,7,2,1,4,4] (by decide +kernel))
      node_1411
      (invalid_excluded a [6,0,7,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,4,7] (by decide +kernel))
      node_1412)

theorem node_1414 : Excluded a [6,0,7,2,1,8,3] :=
  source_excluded a [6,0,7,2,1,8,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1416 : Excluded a [6,0,7,2,1,8,4,3] :=
  source_excluded a [6,0,7,2,1,8,4,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_1417 : Excluded a [6,0,7,2,1,8,4,5] :=
  source_excluded a [6,0,7,2,1,8,4,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_1415 : Excluded a [6,0,7,2,1,8,4] :=
  branch_excluded a [6,0,7,2,1,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,2,1,8,4,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,8,4,1] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,8,4,2] (by decide +kernel))
      node_1416
      (invalid_excluded a [6,0,7,2,1,8,4,4] (by decide +kernel))
      node_1417
      (invalid_excluded a [6,0,7,2,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,8,4,8] (by decide +kernel)))

theorem node_1418 : Excluded a [6,0,7,2,1,8,5] :=
  predecessor_excluded a [6,0,7,2,1,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_1413 : Excluded a [6,0,7,2,1,8] :=
  branch_excluded a [6,0,7,2,1,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,2,1,8,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,8,1] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,8,2] (by decide +kernel))
      node_1414
      node_1415
      node_1418
      (invalid_excluded a [6,0,7,2,1,8,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,8,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,8,8] (by decide +kernel)))

theorem node_1403 : Excluded a [6,0,7,2,1] :=
  branch_excluded a [6,0,7,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,2,1,0] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,2] (by decide +kernel))
      node_1404
      node_1409
      (invalid_excluded a [6,0,7,2,1,5] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,1,7] (by decide +kernel))
      node_1413)

theorem node_1419 : Excluded a [6,0,7,2,3] :=
  predecessor_excluded a [6,0,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1421 : Excluded a [6,0,7,2,8,1] :=
  source_excluded a [6,0,7,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1423 : Excluded a [6,0,7,2,8,3,1] :=
  source_excluded a [6,0,7,2,8,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1424 : Excluded a [6,0,7,2,8,3,4] :=
  predecessor_excluded a [6,0,7,2,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1426 : Excluded a [6,0,7,2,8,3,5,1] :=
  predecessor_excluded a [6,0,7,2,8,3,5,1] 2 0 7 1 (by decide) (by decide +kernel)

theorem node_1427 : Excluded a [6,0,7,2,8,3,5,4] :=
  source_excluded a [6,0,7,2,8,3,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_1425 : Excluded a [6,0,7,2,8,3,5] :=
  branch_excluded a [6,0,7,2,8,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,2,8,3,5,0] (by decide +kernel))
      node_1426
      (invalid_excluded a [6,0,7,2,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,8,3,5,3] (by decide +kernel))
      node_1427
      (invalid_excluded a [6,0,7,2,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,8,3,5,8] (by decide +kernel)))

theorem node_1422 : Excluded a [6,0,7,2,8,3] :=
  branch_excluded a [6,0,7,2,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,2,8,3,0] (by decide +kernel))
      node_1423
      (invalid_excluded a [6,0,7,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,8,3,3] (by decide +kernel))
      node_1424
      node_1425
      (invalid_excluded a [6,0,7,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,8,3,8] (by decide +kernel)))

theorem node_1429 : Excluded a [6,0,7,2,8,4,1] :=
  source_excluded a [6,0,7,2,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1430 : Excluded a [6,0,7,2,8,4,3] :=
  source_excluded a [6,0,7,2,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1431 : Excluded a [6,0,7,2,8,4,5] :=
  predecessor_excluded a [6,0,7,2,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1428 : Excluded a [6,0,7,2,8,4] :=
  branch_excluded a [6,0,7,2,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,2,8,4,0] (by decide +kernel))
      node_1429
      (invalid_excluded a [6,0,7,2,8,4,2] (by decide +kernel))
      node_1430
      (invalid_excluded a [6,0,7,2,8,4,4] (by decide +kernel))
      node_1431
      (invalid_excluded a [6,0,7,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,8,4,8] (by decide +kernel)))

theorem node_1420 : Excluded a [6,0,7,2,8] :=
  branch_excluded a [6,0,7,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,2,8,0] (by decide +kernel))
      node_1421
      (invalid_excluded a [6,0,7,2,8,2] (by decide +kernel))
      node_1422
      node_1428
      (invalid_excluded a [6,0,7,2,8,5] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,8,8] (by decide +kernel)))

theorem node_1402 : Excluded a [6,0,7,2] :=
  branch_excluded a [6,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,2,0] (by decide +kernel))
      node_1403
      (invalid_excluded a [6,0,7,2,2] (by decide +kernel))
      node_1419
      (invalid_excluded a [6,0,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,2,7] (by decide +kernel))
      node_1420)

theorem node_1432 : Excluded a [6,0,7,5] :=
  source_excluded a [6,0,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1433 : Excluded a [6,0,7,8] :=
  predecessor_excluded a [6,0,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_1376 : Excluded a [6,0,7] :=
  branch_excluded a [6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,7,0] (by decide +kernel))
      node_1377
      node_1402
      (invalid_excluded a [6,0,7,3] (by decide +kernel))
      (invalid_excluded a [6,0,7,4] (by decide +kernel))
      node_1432
      (invalid_excluded a [6,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,0,7,7] (by decide +kernel))
      node_1433)

theorem node_1436 : Excluded a [6,0,8,1,2] :=
  predecessor_excluded a [6,0,8,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1440 : Excluded a [6,0,8,1,3,2,4,5] :=
  predecessor_excluded a [6,0,8,1,3,2,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_1439 : Excluded a [6,0,8,1,3,2,4] :=
  branch_excluded a [6,0,8,1,3,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,1,3,2,4,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,4,1] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,4,2] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,4,3] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,4,4] (by decide +kernel))
      node_1440
      (invalid_excluded a [6,0,8,1,3,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,4,8] (by decide +kernel)))

def b_1443 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 0
  | 2 => 8
  | 3 => 1
  | 4 => 3
  | 5 => 2
  | 6 => 5
  | 7 => 4
  | 8 => 7
  | _ => 0

def cert_1443 : LosingRegion (edgeOf a b_1443) 0 :=
  losingMask a b_1443 0 1212513257830133491827712
    (by decide +kernel) (by decide +kernel)

theorem node_1443 : Excluded a [6,0,8,1,3,2,5,4,7] :=
  losing_excluded a [6,0,8,1,3,2,5,4,7] (by decide) b_1443 (by decide +kernel) 2 0 8 cert_1443 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1443 2 0 ∧ 8 ≠ 2 ∧ maskRegion 1212513257830133491827712 2 8; decide +kernel)

theorem node_1442 : Excluded a [6,0,8,1,3,2,5,4] :=
  branch_excluded a [6,0,8,1,3,2,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,1,3,2,5,4,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,5,4,1] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,5,4,2] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,5,4,3] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,5,4,6] (by decide +kernel))
      node_1443
      (invalid_excluded a [6,0,8,1,3,2,5,4,8] (by decide +kernel)))

theorem node_1441 : Excluded a [6,0,8,1,3,2,5] :=
  branch_excluded a [6,0,8,1,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,1,3,2,5,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,5,3] (by decide +kernel))
      node_1442
      (invalid_excluded a [6,0,8,1,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,5,8] (by decide +kernel)))

theorem node_1438 : Excluded a [6,0,8,1,3,2] :=
  branch_excluded a [6,0,8,1,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,1,3,2,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,1] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,3] (by decide +kernel))
      node_1439
      node_1441
      (invalid_excluded a [6,0,8,1,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,2,8] (by decide +kernel)))

theorem node_1444 : Excluded a [6,0,8,1,3,4] :=
  predecessor_excluded a [6,0,8,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1445 : Excluded a [6,0,8,1,3,7] :=
  source_excluded a [6,0,8,1,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1437 : Excluded a [6,0,8,1,3] :=
  branch_excluded a [6,0,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,1] (by decide +kernel))
      node_1438
      (invalid_excluded a [6,0,8,1,3,3] (by decide +kernel))
      node_1444
      (invalid_excluded a [6,0,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,3,6] (by decide +kernel))
      node_1445
      (invalid_excluded a [6,0,8,1,3,8] (by decide +kernel)))

theorem node_1448 : Excluded a [6,0,8,1,7,2,3] :=
  predecessor_excluded a [6,0,8,1,7,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_1449 : Excluded a [6,0,8,1,7,2,4] :=
  source_excluded a [6,0,8,1,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1450 : Excluded a [6,0,8,1,7,2,5] :=
  source_excluded a [6,0,8,1,7,2,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1447 : Excluded a [6,0,8,1,7,2] :=
  branch_excluded a [6,0,8,1,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,1,7,2,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,7,2,2] (by decide +kernel))
      node_1448
      node_1449
      node_1450
      (invalid_excluded a [6,0,8,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,7,2,8] (by decide +kernel)))

theorem node_1452 : Excluded a [6,0,8,1,7,3,2] :=
  predecessor_excluded a [6,0,8,1,7,3,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1453 : Excluded a [6,0,8,1,7,3,4] :=
  source_excluded a [6,0,8,1,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1454 : Excluded a [6,0,8,1,7,3,5] :=
  source_excluded a [6,0,8,1,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1451 : Excluded a [6,0,8,1,7,3] :=
  branch_excluded a [6,0,8,1,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,1,7,3,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,7,3,1] (by decide +kernel))
      node_1452
      (invalid_excluded a [6,0,8,1,7,3,3] (by decide +kernel))
      node_1453
      node_1454
      (invalid_excluded a [6,0,8,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,7,3,8] (by decide +kernel)))

theorem node_1455 : Excluded a [6,0,8,1,7,4] :=
  predecessor_excluded a [6,0,8,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1446 : Excluded a [6,0,8,1,7] :=
  branch_excluded a [6,0,8,1,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,1,7,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,7,1] (by decide +kernel))
      node_1447
      node_1451
      node_1455
      (invalid_excluded a [6,0,8,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,7,8] (by decide +kernel)))

theorem node_1435 : Excluded a [6,0,8,1] :=
  branch_excluded a [6,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,1] (by decide +kernel))
      node_1436
      node_1437
      (invalid_excluded a [6,0,8,1,4] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,1,6] (by decide +kernel))
      node_1446
      (invalid_excluded a [6,0,8,1,8] (by decide +kernel)))

theorem node_1459 : Excluded a [6,0,8,2,1,3,4] :=
  predecessor_excluded a [6,0,8,2,1,3,4] 0 4 5 6 (by decide) (by decide +kernel)

def b_1462 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 0
  | 2 => 8
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 5
  | 7 => 4
  | 8 => 7
  | _ => 0

def cert_1462 : LosingRegion (edgeOf a b_1462) 0 :=
  losingMask a b_1462 0 1212475754402530532000768
    (by decide +kernel) (by decide +kernel)

theorem node_1462 : Excluded a [6,0,8,2,1,3,5,4,7] :=
  losing_excluded a [6,0,8,2,1,3,5,4,7] (by decide) b_1462 (by decide +kernel) 2 0 7 cert_1462 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1462 2 0 ∧ 7 ≠ 2 ∧ maskRegion 1212475754402530532000768 2 7; decide +kernel)

theorem node_1461 : Excluded a [6,0,8,2,1,3,5,4] :=
  branch_excluded a [6,0,8,2,1,3,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,2,1,3,5,4,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,5,4,1] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,5,4,2] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,5,4,3] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,5,4,6] (by decide +kernel))
      node_1462
      (invalid_excluded a [6,0,8,2,1,3,5,4,8] (by decide +kernel)))

theorem node_1460 : Excluded a [6,0,8,2,1,3,5] :=
  branch_excluded a [6,0,8,2,1,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,2,1,3,5,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,5,3] (by decide +kernel))
      node_1461
      (invalid_excluded a [6,0,8,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,5,8] (by decide +kernel)))

theorem node_1458 : Excluded a [6,0,8,2,1,3] :=
  branch_excluded a [6,0,8,2,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,2,1,3,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,3] (by decide +kernel))
      node_1459
      node_1460
      (invalid_excluded a [6,0,8,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,3,8] (by decide +kernel)))

def b_1466 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 0
  | 2 => 8
  | 3 => 2
  | 4 => 1
  | 5 => 4
  | 6 => 3
  | 7 => 5
  | 8 => 7
  | _ => 0

def cert_1466 : LosingRegion (edgeOf a b_1466) 0 :=
  losingMask a b_1466 0 1212512821701458890064896
    (by decide +kernel) (by decide +kernel)

theorem node_1466 : Excluded a [6,0,8,2,1,4,3,5,7] :=
  losing_excluded a [6,0,8,2,1,4,3,5,7] (by decide) b_1466 (by decide +kernel) 2 0 7 cert_1466 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1466 2 0 ∧ 7 ≠ 2 ∧ maskRegion 1212512821701458890064896 2 7; decide +kernel)

theorem node_1465 : Excluded a [6,0,8,2,1,4,3,5] :=
  branch_excluded a [6,0,8,2,1,4,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,2,1,4,3,5,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,3,5,1] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,3,5,3] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,3,5,4] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,3,5,6] (by decide +kernel))
      node_1466
      (invalid_excluded a [6,0,8,2,1,4,3,5,8] (by decide +kernel)))

theorem node_1464 : Excluded a [6,0,8,2,1,4,3] :=
  branch_excluded a [6,0,8,2,1,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,2,1,4,3,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,3,1] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,3,2] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,3,4] (by decide +kernel))
      node_1465
      (invalid_excluded a [6,0,8,2,1,4,3,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,3,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,3,8] (by decide +kernel)))

theorem node_1467 : Excluded a [6,0,8,2,1,4,5] :=
  predecessor_excluded a [6,0,8,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1463 : Excluded a [6,0,8,2,1,4] :=
  branch_excluded a [6,0,8,2,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,2,1,4,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,2] (by decide +kernel))
      node_1464
      (invalid_excluded a [6,0,8,2,1,4,4] (by decide +kernel))
      node_1467
      (invalid_excluded a [6,0,8,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,4,8] (by decide +kernel)))

theorem node_1468 : Excluded a [6,0,8,2,1,7] :=
  source_excluded a [6,0,8,2,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1457 : Excluded a [6,0,8,2,1] :=
  branch_excluded a [6,0,8,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,2,1,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,2] (by decide +kernel))
      node_1458
      node_1463
      (invalid_excluded a [6,0,8,2,1,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,1,6] (by decide +kernel))
      node_1468
      (invalid_excluded a [6,0,8,2,1,8] (by decide +kernel)))

theorem node_1469 : Excluded a [6,0,8,2,3] :=
  predecessor_excluded a [6,0,8,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1471 : Excluded a [6,0,8,2,7,1] :=
  source_excluded a [6,0,8,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1473 : Excluded a [6,0,8,2,7,3,1] :=
  source_excluded a [6,0,8,2,7,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1474 : Excluded a [6,0,8,2,7,3,4] :=
  source_excluded a [6,0,8,2,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1475 : Excluded a [6,0,8,2,7,3,5] :=
  source_excluded a [6,0,8,2,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1472 : Excluded a [6,0,8,2,7,3] :=
  branch_excluded a [6,0,8,2,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,2,7,3,0] (by decide +kernel))
      node_1473
      (invalid_excluded a [6,0,8,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,7,3,3] (by decide +kernel))
      node_1474
      node_1475
      (invalid_excluded a [6,0,8,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,7,3,8] (by decide +kernel)))

theorem node_1476 : Excluded a [6,0,8,2,7,4] :=
  predecessor_excluded a [6,0,8,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1470 : Excluded a [6,0,8,2,7] :=
  branch_excluded a [6,0,8,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,2,7,0] (by decide +kernel))
      node_1471
      (invalid_excluded a [6,0,8,2,7,2] (by decide +kernel))
      node_1472
      node_1476
      (invalid_excluded a [6,0,8,2,7,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,7,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,7,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,7,8] (by decide +kernel)))

theorem node_1456 : Excluded a [6,0,8,2] :=
  branch_excluded a [6,0,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,2,0] (by decide +kernel))
      node_1457
      (invalid_excluded a [6,0,8,2,2] (by decide +kernel))
      node_1469
      (invalid_excluded a [6,0,8,2,4] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,2,6] (by decide +kernel))
      node_1470
      (invalid_excluded a [6,0,8,2,8] (by decide +kernel)))

theorem node_1477 : Excluded a [6,0,8,5] :=
  source_excluded a [6,0,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1480 : Excluded a [6,0,8,7,1,2] :=
  predecessor_excluded a [6,0,8,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1481 : Excluded a [6,0,8,7,1,3] :=
  predecessor_excluded a [6,0,8,7,1,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1483 : Excluded a [6,0,8,7,1,4,2] :=
  predecessor_excluded a [6,0,8,7,1,4,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1484 : Excluded a [6,0,8,7,1,4,3] :=
  source_excluded a [6,0,8,7,1,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1485 : Excluded a [6,0,8,7,1,4,5] :=
  predecessor_excluded a [6,0,8,7,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1482 : Excluded a [6,0,8,7,1,4] :=
  branch_excluded a [6,0,8,7,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,7,1,4,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,1,4,1] (by decide +kernel))
      node_1483
      node_1484
      (invalid_excluded a [6,0,8,7,1,4,4] (by decide +kernel))
      node_1485
      (invalid_excluded a [6,0,8,7,1,4,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,1,4,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,1,4,8] (by decide +kernel)))

theorem node_1479 : Excluded a [6,0,8,7,1] :=
  branch_excluded a [6,0,8,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,7,1,0] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,1,1] (by decide +kernel))
      node_1480
      node_1481
      node_1482
      (invalid_excluded a [6,0,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,1,8] (by decide +kernel)))

theorem node_1487 : Excluded a [6,0,8,7,2,1] :=
  source_excluded a [6,0,8,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1488 : Excluded a [6,0,8,7,2,3] :=
  predecessor_excluded a [6,0,8,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1490 : Excluded a [6,0,8,7,2,4,1] :=
  source_excluded a [6,0,8,7,2,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1491 : Excluded a [6,0,8,7,2,4,3] :=
  source_excluded a [6,0,8,7,2,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1492 : Excluded a [6,0,8,7,2,4,5] :=
  predecessor_excluded a [6,0,8,7,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1489 : Excluded a [6,0,8,7,2,4] :=
  branch_excluded a [6,0,8,7,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,7,2,4,0] (by decide +kernel))
      node_1490
      (invalid_excluded a [6,0,8,7,2,4,2] (by decide +kernel))
      node_1491
      (invalid_excluded a [6,0,8,7,2,4,4] (by decide +kernel))
      node_1492
      (invalid_excluded a [6,0,8,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,2,4,8] (by decide +kernel)))

theorem node_1486 : Excluded a [6,0,8,7,2] :=
  branch_excluded a [6,0,8,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,7,2,0] (by decide +kernel))
      node_1487
      (invalid_excluded a [6,0,8,7,2,2] (by decide +kernel))
      node_1488
      node_1489
      (invalid_excluded a [6,0,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,2,8] (by decide +kernel)))

theorem node_1494 : Excluded a [6,0,8,7,3,1] :=
  source_excluded a [6,0,8,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1496 : Excluded a [6,0,8,7,3,2,1] :=
  source_excluded a [6,0,8,7,3,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1497 : Excluded a [6,0,8,7,3,2,4] :=
  source_excluded a [6,0,8,7,3,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1499 : Excluded a [6,0,8,7,3,2,5,1] :=
  predecessor_excluded a [6,0,8,7,3,2,5,1] 2 0 7 1 (by decide) (by decide +kernel)

theorem node_1500 : Excluded a [6,0,8,7,3,2,5,4] :=
  source_excluded a [6,0,8,7,3,2,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_1498 : Excluded a [6,0,8,7,3,2,5] :=
  branch_excluded a [6,0,8,7,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,7,3,2,5,0] (by decide +kernel))
      node_1499
      (invalid_excluded a [6,0,8,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,3,2,5,3] (by decide +kernel))
      node_1500
      (invalid_excluded a [6,0,8,7,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,3,2,5,8] (by decide +kernel)))

theorem node_1495 : Excluded a [6,0,8,7,3,2] :=
  branch_excluded a [6,0,8,7,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,7,3,2,0] (by decide +kernel))
      node_1496
      (invalid_excluded a [6,0,8,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,3,2,3] (by decide +kernel))
      node_1497
      node_1498
      (invalid_excluded a [6,0,8,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,3,2,8] (by decide +kernel)))

theorem node_1501 : Excluded a [6,0,8,7,3,4] :=
  predecessor_excluded a [6,0,8,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1493 : Excluded a [6,0,8,7,3] :=
  branch_excluded a [6,0,8,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,7,3,0] (by decide +kernel))
      node_1494
      node_1495
      (invalid_excluded a [6,0,8,7,3,3] (by decide +kernel))
      node_1501
      (invalid_excluded a [6,0,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,3,8] (by decide +kernel)))

theorem node_1478 : Excluded a [6,0,8,7] :=
  branch_excluded a [6,0,8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,7,0] (by decide +kernel))
      node_1479
      node_1486
      node_1493
      (invalid_excluded a [6,0,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,0,8,7,8] (by decide +kernel)))

theorem node_1434 : Excluded a [6,0,8] :=
  branch_excluded a [6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,8,0] (by decide +kernel))
      node_1435
      node_1456
      (invalid_excluded a [6,0,8,3] (by decide +kernel))
      (invalid_excluded a [6,0,8,4] (by decide +kernel))
      node_1477
      (invalid_excluded a [6,0,8,6] (by decide +kernel))
      node_1478
      (invalid_excluded a [6,0,8,8] (by decide +kernel)))

theorem node_1325 : Excluded a [6,0] :=
  branch_excluded a [6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0,0] (by decide +kernel))
      node_1326
      (invalid_excluded a [6,0,2] (by decide +kernel))
      (invalid_excluded a [6,0,3] (by decide +kernel))
      node_1327
      node_1328
      (invalid_excluded a [6,0,6] (by decide +kernel))
      node_1376
      node_1434)

theorem node_1502 : Excluded a [6,3] :=
  source_excluded a [6,3] 1 0 2 (by decide) (by decide +kernel)

theorem node_1505 : Excluded a [6,4,0,1] :=
  source_excluded a [6,4,0,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1506 : Excluded a [6,4,0,2] :=
  source_excluded a [6,4,0,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1507 : Excluded a [6,4,0,5] :=
  source_excluded a [6,4,0,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1510 : Excluded a [6,4,0,7,1,2] :=
  predecessor_excluded a [6,4,0,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1511 : Excluded a [6,4,0,7,1,3] :=
  predecessor_excluded a [6,4,0,7,1,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1513 : Excluded a [6,4,0,7,1,8,2] :=
  predecessor_excluded a [6,4,0,7,1,8,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1514 : Excluded a [6,4,0,7,1,8,3] :=
  source_excluded a [6,4,0,7,1,8,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1515 : Excluded a [6,4,0,7,1,8,5] :=
  predecessor_excluded a [6,4,0,7,1,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_1512 : Excluded a [6,4,0,7,1,8] :=
  branch_excluded a [6,4,0,7,1,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,1,8,0] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,1,8,1] (by decide +kernel))
      node_1513
      node_1514
      (invalid_excluded a [6,4,0,7,1,8,4] (by decide +kernel))
      node_1515
      (invalid_excluded a [6,4,0,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,1,8,8] (by decide +kernel)))

theorem node_1509 : Excluded a [6,4,0,7,1] :=
  branch_excluded a [6,4,0,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,1,0] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,1,1] (by decide +kernel))
      node_1510
      node_1511
      (invalid_excluded a [6,4,0,7,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,1,7] (by decide +kernel))
      node_1512)

theorem node_1516 : Excluded a [6,4,0,7,2] :=
  source_excluded a [6,4,0,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1517 : Excluded a [6,4,0,7,3] :=
  predecessor_excluded a [6,4,0,7,3] 0 3 1 4 (by decide) (by decide +kernel)

theorem node_1518 : Excluded a [6,4,0,7,8] :=
  predecessor_excluded a [6,4,0,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1508 : Excluded a [6,4,0,7] :=
  branch_excluded a [6,4,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,0] (by decide +kernel))
      node_1509
      node_1516
      node_1517
      (invalid_excluded a [6,4,0,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,7] (by decide +kernel))
      node_1518)

theorem node_1521 : Excluded a [6,4,0,8,1,2] :=
  predecessor_excluded a [6,4,0,8,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1523 : Excluded a [6,4,0,8,1,3,2] :=
  predecessor_excluded a [6,4,0,8,1,3,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1525 : Excluded a [6,4,0,8,1,3,5,2] :=
  predecessor_excluded a [6,4,0,8,1,3,5,2] 1 0 7 2 (by decide) (by decide +kernel)

theorem node_1524 : Excluded a [6,4,0,8,1,3,5] :=
  branch_excluded a [6,4,0,8,1,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,1,3,5,0] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,1,3,5,1] (by decide +kernel))
      node_1525
      (invalid_excluded a [6,4,0,8,1,3,5,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,1,3,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,1,3,5,8] (by decide +kernel)))

theorem node_1522 : Excluded a [6,4,0,8,1,3] :=
  branch_excluded a [6,4,0,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,1,3,1] (by decide +kernel))
      node_1523
      (invalid_excluded a [6,4,0,8,1,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,1,3,4] (by decide +kernel))
      node_1524
      (invalid_excluded a [6,4,0,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,1,3,8] (by decide +kernel)))

theorem node_1526 : Excluded a [6,4,0,8,1,7] :=
  source_excluded a [6,4,0,8,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1520 : Excluded a [6,4,0,8,1] :=
  branch_excluded a [6,4,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,1,1] (by decide +kernel))
      node_1521
      node_1522
      (invalid_excluded a [6,4,0,8,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,1,6] (by decide +kernel))
      node_1526
      (invalid_excluded a [6,4,0,8,1,8] (by decide +kernel)))

theorem node_1527 : Excluded a [6,4,0,8,2] :=
  source_excluded a [6,4,0,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1528 : Excluded a [6,4,0,8,3] :=
  predecessor_excluded a [6,4,0,8,3] 0 3 1 4 (by decide) (by decide +kernel)

theorem node_1530 : Excluded a [6,4,0,8,7,1] :=
  source_excluded a [6,4,0,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1532 : Excluded a [6,4,0,8,7,2,1] :=
  source_excluded a [6,4,0,8,7,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1533 : Excluded a [6,4,0,8,7,2,3] :=
  predecessor_excluded a [6,4,0,8,7,2,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_1534 : Excluded a [6,4,0,8,7,2,5] :=
  source_excluded a [6,4,0,8,7,2,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1531 : Excluded a [6,4,0,8,7,2] :=
  branch_excluded a [6,4,0,8,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,2,0] (by decide +kernel))
      node_1532
      (invalid_excluded a [6,4,0,8,7,2,2] (by decide +kernel))
      node_1533
      (invalid_excluded a [6,4,0,8,7,2,4] (by decide +kernel))
      node_1534
      (invalid_excluded a [6,4,0,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,8] (by decide +kernel)))

theorem node_1536 : Excluded a [6,4,0,8,7,3,1] :=
  source_excluded a [6,4,0,8,7,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1537 : Excluded a [6,4,0,8,7,3,2] :=
  predecessor_excluded a [6,4,0,8,7,3,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1538 : Excluded a [6,4,0,8,7,3,5] :=
  source_excluded a [6,4,0,8,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1535 : Excluded a [6,4,0,8,7,3] :=
  branch_excluded a [6,4,0,8,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,3,0] (by decide +kernel))
      node_1536
      node_1537
      (invalid_excluded a [6,4,0,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,4] (by decide +kernel))
      node_1538
      (invalid_excluded a [6,4,0,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,8] (by decide +kernel)))

theorem node_1529 : Excluded a [6,4,0,8,7] :=
  branch_excluded a [6,4,0,8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,0] (by decide +kernel))
      node_1530
      node_1531
      node_1535
      (invalid_excluded a [6,4,0,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,8] (by decide +kernel)))

theorem node_1519 : Excluded a [6,4,0,8] :=
  branch_excluded a [6,4,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,0] (by decide +kernel))
      node_1520
      node_1527
      node_1528
      (invalid_excluded a [6,4,0,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,6] (by decide +kernel))
      node_1529
      (invalid_excluded a [6,4,0,8,8] (by decide +kernel)))

theorem node_1504 : Excluded a [6,4,0] :=
  branch_excluded a [6,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,0] (by decide +kernel))
      node_1505
      node_1506
      (invalid_excluded a [6,4,0,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,4] (by decide +kernel))
      node_1507
      (invalid_excluded a [6,4,0,6] (by decide +kernel))
      node_1508
      node_1519)

theorem node_1539 : Excluded a [6,4,1] :=
  predecessor_excluded a [6,4,1] 0 4 2 1 (by decide) (by decide +kernel)

theorem node_1540 : Excluded a [6,4,5] :=
  predecessor_excluded a [6,4,5] 0 5 1 2 (by decide) (by decide +kernel)

theorem node_1543 : Excluded a [6,4,7,0,1] :=
  predecessor_excluded a [6,4,7,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1544 : Excluded a [6,4,7,0,2] :=
  source_excluded a [6,4,7,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1545 : Excluded a [6,4,7,0,3] :=
  predecessor_excluded a [6,4,7,0,3] 0 3 1 4 (by decide) (by decide +kernel)

theorem node_1547 : Excluded a [6,4,7,0,8,1] :=
  source_excluded a [6,4,7,0,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1548 : Excluded a [6,4,7,0,8,2] :=
  predecessor_excluded a [6,4,7,0,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1550 : Excluded a [6,4,7,0,8,3,1] :=
  source_excluded a [6,4,7,0,8,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1551 : Excluded a [6,4,7,0,8,3,2] :=
  source_excluded a [6,4,7,0,8,3,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1554 : Excluded a [6,4,7,0,8,3,5,1,2] :=
  predecessor_excluded a [6,4,7,0,8,3,5,1,2] 0 2 7 8 (by decide) (by decide +kernel)

theorem node_1553 : Excluded a [6,4,7,0,8,3,5,1] :=
  branch_excluded a [6,4,7,0,8,3,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,0,8,3,5,1,0] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,1,1] (by decide +kernel))
      node_1554
      (invalid_excluded a [6,4,7,0,8,3,5,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,1,8] (by decide +kernel)))

theorem node_1556 : Excluded a [6,4,7,0,8,3,5,2,1] :=
  source_excluded a [6,4,7,0,8,3,5,2,1] 8 2 0 (by decide) (by decide +kernel)

theorem node_1555 : Excluded a [6,4,7,0,8,3,5,2] :=
  branch_excluded a [6,4,7,0,8,3,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,0,8,3,5,2,0] (by decide +kernel))
      node_1556
      (invalid_excluded a [6,4,7,0,8,3,5,2,2] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,2,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,2,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,2,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,2,8] (by decide +kernel)))

theorem node_1552 : Excluded a [6,4,7,0,8,3,5] :=
  branch_excluded a [6,4,7,0,8,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,0,8,3,5,0] (by decide +kernel))
      node_1553
      node_1555
      (invalid_excluded a [6,4,7,0,8,3,5,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,5,8] (by decide +kernel)))

theorem node_1549 : Excluded a [6,4,7,0,8,3] :=
  branch_excluded a [6,4,7,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,0,8,3,0] (by decide +kernel))
      node_1550
      node_1551
      (invalid_excluded a [6,4,7,0,8,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,4] (by decide +kernel))
      node_1552
      (invalid_excluded a [6,4,7,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,3,8] (by decide +kernel)))

theorem node_1546 : Excluded a [6,4,7,0,8] :=
  branch_excluded a [6,4,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,0,8,0] (by decide +kernel))
      node_1547
      node_1548
      node_1549
      (invalid_excluded a [6,4,7,0,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,8,8] (by decide +kernel)))

theorem node_1542 : Excluded a [6,4,7,0] :=
  branch_excluded a [6,4,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,0,0] (by decide +kernel))
      node_1543
      node_1544
      node_1545
      (invalid_excluded a [6,4,7,0,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,0,7] (by decide +kernel))
      node_1546)

theorem node_1557 : Excluded a [6,4,7,1] :=
  source_excluded a [6,4,7,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1558 : Excluded a [6,4,7,2] :=
  source_excluded a [6,4,7,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1559 : Excluded a [6,4,7,5] :=
  source_excluded a [6,4,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1560 : Excluded a [6,4,7,8] :=
  predecessor_excluded a [6,4,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_1541 : Excluded a [6,4,7] :=
  branch_excluded a [6,4,7] (by decide)
    (fin9_cases _
      node_1542
      node_1557
      node_1558
      (invalid_excluded a [6,4,7,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,4] (by decide +kernel))
      node_1559
      (invalid_excluded a [6,4,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,7] (by decide +kernel))
      node_1560)

theorem node_1562 : Excluded a [6,4,8,0] :=
  predecessor_excluded a [6,4,8,0] 1 0 2 3 (by decide) (by decide +kernel)

theorem node_1563 : Excluded a [6,4,8,1] :=
  source_excluded a [6,4,8,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1564 : Excluded a [6,4,8,2] :=
  source_excluded a [6,4,8,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_1565 : Excluded a [6,4,8,5] :=
  source_excluded a [6,4,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1567 : Excluded a [6,4,8,7,0] :=
  predecessor_excluded a [6,4,8,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1569 : Excluded a [6,4,8,7,1,0] :=
  source_excluded a [6,4,8,7,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1570 : Excluded a [6,4,8,7,1,2] :=
  predecessor_excluded a [6,4,8,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1571 : Excluded a [6,4,8,7,1,3] :=
  predecessor_excluded a [6,4,8,7,1,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1568 : Excluded a [6,4,8,7,1] :=
  branch_excluded a [6,4,8,7,1] (by decide)
    (fin9_cases _
      node_1569
      (invalid_excluded a [6,4,8,7,1,1] (by decide +kernel))
      node_1570
      node_1571
      (invalid_excluded a [6,4,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,1,8] (by decide +kernel)))

theorem node_1572 : Excluded a [6,4,8,7,2] :=
  source_excluded a [6,4,8,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1573 : Excluded a [6,4,8,7,3] :=
  predecessor_excluded a [6,4,8,7,3] 0 3 1 4 (by decide) (by decide +kernel)

theorem node_1566 : Excluded a [6,4,8,7] :=
  branch_excluded a [6,4,8,7] (by decide)
    (fin9_cases _
      node_1567
      node_1568
      node_1572
      node_1573
      (invalid_excluded a [6,4,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,8] (by decide +kernel)))

theorem node_1561 : Excluded a [6,4,8] :=
  branch_excluded a [6,4,8] (by decide)
    (fin9_cases _
      node_1562
      node_1563
      node_1564
      (invalid_excluded a [6,4,8,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,4] (by decide +kernel))
      node_1565
      (invalid_excluded a [6,4,8,6] (by decide +kernel))
      node_1566
      (invalid_excluded a [6,4,8,8] (by decide +kernel)))

theorem node_1503 : Excluded a [6,4] :=
  branch_excluded a [6,4] (by decide)
    (fin9_cases _
      node_1504
      node_1539
      (invalid_excluded a [6,4,2] (by decide +kernel))
      (invalid_excluded a [6,4,3] (by decide +kernel))
      (invalid_excluded a [6,4,4] (by decide +kernel))
      node_1540
      (invalid_excluded a [6,4,6] (by decide +kernel))
      node_1541
      node_1561)

theorem node_1576 : Excluded a [6,5,0,1] :=
  predecessor_excluded a [6,5,0,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1578 : Excluded a [6,5,0,2,1] :=
  source_excluded a [6,5,0,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1579 : Excluded a [6,5,0,2,3] :=
  predecessor_excluded a [6,5,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1581 : Excluded a [6,5,0,2,7,1] :=
  source_excluded a [6,5,0,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1582 : Excluded a [6,5,0,2,7,3] :=
  predecessor_excluded a [6,5,0,2,7,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_1583 : Excluded a [6,5,0,2,7,4] :=
  predecessor_excluded a [6,5,0,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1584 : Excluded a [6,5,0,2,7,8] :=
  predecessor_excluded a [6,5,0,2,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_1580 : Excluded a [6,5,0,2,7] :=
  branch_excluded a [6,5,0,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0,2,7,0] (by decide +kernel))
      node_1581
      (invalid_excluded a [6,5,0,2,7,2] (by decide +kernel))
      node_1582
      node_1583
      (invalid_excluded a [6,5,0,2,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,7,7] (by decide +kernel))
      node_1584)

theorem node_1586 : Excluded a [6,5,0,2,8,1] :=
  source_excluded a [6,5,0,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1587 : Excluded a [6,5,0,2,8,3] :=
  predecessor_excluded a [6,5,0,2,8,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_1589 : Excluded a [6,5,0,2,8,4,1] :=
  source_excluded a [6,5,0,2,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1592 : Excluded a [6,5,0,2,8,4,3,1,7] :=
  predecessor_excluded a [6,5,0,2,8,4,3,1,7] 2 1 8 7 (by decide) (by decide +kernel)

theorem node_1591 : Excluded a [6,5,0,2,8,4,3,1] :=
  branch_excluded a [6,5,0,2,8,4,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0,2,8,4,3,1,0] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,3,1,1] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,3,1,2] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,3,1,3] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,3,1,4] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,3,1,5] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,3,1,6] (by decide +kernel))
      node_1592
      (invalid_excluded a [6,5,0,2,8,4,3,1,8] (by decide +kernel)))

theorem node_1590 : Excluded a [6,5,0,2,8,4,3] :=
  branch_excluded a [6,5,0,2,8,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0,2,8,4,3,0] (by decide +kernel))
      node_1591
      (invalid_excluded a [6,5,0,2,8,4,3,2] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,3,8] (by decide +kernel)))

theorem node_1588 : Excluded a [6,5,0,2,8,4] :=
  branch_excluded a [6,5,0,2,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0,2,8,4,0] (by decide +kernel))
      node_1589
      (invalid_excluded a [6,5,0,2,8,4,2] (by decide +kernel))
      node_1590
      (invalid_excluded a [6,5,0,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,4,8] (by decide +kernel)))

theorem node_1593 : Excluded a [6,5,0,2,8,7] :=
  source_excluded a [6,5,0,2,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1585 : Excluded a [6,5,0,2,8] :=
  branch_excluded a [6,5,0,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0,2,8,0] (by decide +kernel))
      node_1586
      (invalid_excluded a [6,5,0,2,8,2] (by decide +kernel))
      node_1587
      node_1588
      (invalid_excluded a [6,5,0,2,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,8,6] (by decide +kernel))
      node_1593
      (invalid_excluded a [6,5,0,2,8,8] (by decide +kernel)))

theorem node_1577 : Excluded a [6,5,0,2] :=
  branch_excluded a [6,5,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0,2,0] (by decide +kernel))
      node_1578
      (invalid_excluded a [6,5,0,2,2] (by decide +kernel))
      node_1579
      (invalid_excluded a [6,5,0,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,0,2,6] (by decide +kernel))
      node_1580
      node_1585)

theorem node_1595 : Excluded a [6,5,0,7,1] :=
  source_excluded a [6,5,0,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1596 : Excluded a [6,5,0,7,2] :=
  source_excluded a [6,5,0,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1598 : Excluded a [6,5,0,7,3,1] :=
  source_excluded a [6,5,0,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1599 : Excluded a [6,5,0,7,3,2] :=
  source_excluded a [6,5,0,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1600 : Excluded a [6,5,0,7,3,4] :=
  predecessor_excluded a [6,5,0,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1602 : Excluded a [6,5,0,7,3,8,1] :=
  source_excluded a [6,5,0,7,3,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1603 : Excluded a [6,5,0,7,3,8,2] :=
  predecessor_excluded a [6,5,0,7,3,8,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1604 : Excluded a [6,5,0,7,3,8,4] :=
  source_excluded a [6,5,0,7,3,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1601 : Excluded a [6,5,0,7,3,8] :=
  branch_excluded a [6,5,0,7,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0,7,3,8,0] (by decide +kernel))
      node_1602
      node_1603
      (invalid_excluded a [6,5,0,7,3,8,3] (by decide +kernel))
      node_1604
      (invalid_excluded a [6,5,0,7,3,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,0,7,3,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,0,7,3,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,0,7,3,8,8] (by decide +kernel)))

theorem node_1597 : Excluded a [6,5,0,7,3] :=
  branch_excluded a [6,5,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0,7,3,0] (by decide +kernel))
      node_1598
      node_1599
      (invalid_excluded a [6,5,0,7,3,3] (by decide +kernel))
      node_1600
      (invalid_excluded a [6,5,0,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,0,7,3,7] (by decide +kernel))
      node_1601)

theorem node_1605 : Excluded a [6,5,0,7,8] :=
  predecessor_excluded a [6,5,0,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1594 : Excluded a [6,5,0,7] :=
  branch_excluded a [6,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0,7,0] (by decide +kernel))
      node_1595
      node_1596
      node_1597
      (invalid_excluded a [6,5,0,7,4] (by decide +kernel))
      (invalid_excluded a [6,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,0,7,7] (by decide +kernel))
      node_1605)

theorem node_1607 : Excluded a [6,5,0,8,1] :=
  source_excluded a [6,5,0,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1608 : Excluded a [6,5,0,8,2] :=
  source_excluded a [6,5,0,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1610 : Excluded a [6,5,0,8,3,1] :=
  source_excluded a [6,5,0,8,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1611 : Excluded a [6,5,0,8,3,2] :=
  source_excluded a [6,5,0,8,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1612 : Excluded a [6,5,0,8,3,4] :=
  predecessor_excluded a [6,5,0,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1613 : Excluded a [6,5,0,8,3,7] :=
  source_excluded a [6,5,0,8,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1609 : Excluded a [6,5,0,8,3] :=
  branch_excluded a [6,5,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0,8,3,0] (by decide +kernel))
      node_1610
      node_1611
      (invalid_excluded a [6,5,0,8,3,3] (by decide +kernel))
      node_1612
      (invalid_excluded a [6,5,0,8,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,0,8,3,6] (by decide +kernel))
      node_1613
      (invalid_excluded a [6,5,0,8,3,8] (by decide +kernel)))

theorem node_1615 : Excluded a [6,5,0,8,7,1] :=
  source_excluded a [6,5,0,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1616 : Excluded a [6,5,0,8,7,2] :=
  source_excluded a [6,5,0,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1617 : Excluded a [6,5,0,8,7,3] :=
  predecessor_excluded a [6,5,0,8,7,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_1618 : Excluded a [6,5,0,8,7,4] :=
  predecessor_excluded a [6,5,0,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1614 : Excluded a [6,5,0,8,7] :=
  branch_excluded a [6,5,0,8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0,8,7,0] (by decide +kernel))
      node_1615
      node_1616
      node_1617
      node_1618
      (invalid_excluded a [6,5,0,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,0,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,0,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,5,0,8,7,8] (by decide +kernel)))

theorem node_1606 : Excluded a [6,5,0,8] :=
  branch_excluded a [6,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0,8,0] (by decide +kernel))
      node_1607
      node_1608
      node_1609
      (invalid_excluded a [6,5,0,8,4] (by decide +kernel))
      (invalid_excluded a [6,5,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,0,8,6] (by decide +kernel))
      node_1614
      (invalid_excluded a [6,5,0,8,8] (by decide +kernel)))

theorem node_1575 : Excluded a [6,5,0] :=
  branch_excluded a [6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,0,0] (by decide +kernel))
      node_1576
      node_1577
      (invalid_excluded a [6,5,0,3] (by decide +kernel))
      (invalid_excluded a [6,5,0,4] (by decide +kernel))
      (invalid_excluded a [6,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,5,0,6] (by decide +kernel))
      node_1594
      node_1606)

theorem node_1621 : Excluded a [6,5,1,0,2] :=
  source_excluded a [6,5,1,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1623 : Excluded a [6,5,1,0,3,2] :=
  source_excluded a [6,5,1,0,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1624 : Excluded a [6,5,1,0,3,4] :=
  predecessor_excluded a [6,5,1,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1625 : Excluded a [6,5,1,0,3,7] :=
  source_excluded a [6,5,1,0,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1627 : Excluded a [6,5,1,0,3,8,2] :=
  predecessor_excluded a [6,5,1,0,3,8,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1630 : Excluded a [6,5,1,0,3,8,4,2,7] :=
  predecessor_excluded a [6,5,1,0,3,8,4,2,7] 0 7 5 8 (by decide) (by decide +kernel)

theorem node_1629 : Excluded a [6,5,1,0,3,8,4,2] :=
  branch_excluded a [6,5,1,0,3,8,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,1,0,3,8,4,2,0] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,4,2,1] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,4,2,2] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,4,2,3] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,4,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,4,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,4,2,6] (by decide +kernel))
      node_1630
      (invalid_excluded a [6,5,1,0,3,8,4,2,8] (by decide +kernel)))

theorem node_1628 : Excluded a [6,5,1,0,3,8,4] :=
  branch_excluded a [6,5,1,0,3,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,1,0,3,8,4,0] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,4,1] (by decide +kernel))
      node_1629
      (invalid_excluded a [6,5,1,0,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,4,4] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,4,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,4,8] (by decide +kernel)))

theorem node_1626 : Excluded a [6,5,1,0,3,8] :=
  branch_excluded a [6,5,1,0,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,1,0,3,8,0] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,1] (by decide +kernel))
      node_1627
      (invalid_excluded a [6,5,1,0,3,8,3] (by decide +kernel))
      node_1628
      (invalid_excluded a [6,5,1,0,3,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,8,8] (by decide +kernel)))

theorem node_1622 : Excluded a [6,5,1,0,3] :=
  branch_excluded a [6,5,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,1] (by decide +kernel))
      node_1623
      (invalid_excluded a [6,5,1,0,3,3] (by decide +kernel))
      node_1624
      (invalid_excluded a [6,5,1,0,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,3,6] (by decide +kernel))
      node_1625
      node_1626)

theorem node_1632 : Excluded a [6,5,1,0,7,2] :=
  source_excluded a [6,5,1,0,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1633 : Excluded a [6,5,1,0,7,3] :=
  predecessor_excluded a [6,5,1,0,7,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_1634 : Excluded a [6,5,1,0,7,4] :=
  predecessor_excluded a [6,5,1,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1635 : Excluded a [6,5,1,0,7,8] :=
  predecessor_excluded a [6,5,1,0,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_1631 : Excluded a [6,5,1,0,7] :=
  branch_excluded a [6,5,1,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,1,0,7,0] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,7,1] (by decide +kernel))
      node_1632
      node_1633
      node_1634
      (invalid_excluded a [6,5,1,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,7,7] (by decide +kernel))
      node_1635)

theorem node_1637 : Excluded a [6,5,1,0,8,2] :=
  source_excluded a [6,5,1,0,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1638 : Excluded a [6,5,1,0,8,3] :=
  predecessor_excluded a [6,5,1,0,8,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_1640 : Excluded a [6,5,1,0,8,4,2] :=
  predecessor_excluded a [6,5,1,0,8,4,2] 3 2 0 6 (by decide) (by decide +kernel)

def b_1643 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 5
  | 2 => 1
  | 3 => 0
  | 4 => 8
  | 5 => 4
  | 6 => 3
  | 7 => 2
  | 8 => 7
  | _ => 0

def cert_1643 : LosingRegion (edgeOf a b_1643) 1 :=
  losingMask a b_1643 1 1210114499164850615222273
    (by decide +kernel) (by decide +kernel)

theorem node_1643 : Excluded a [6,5,1,0,8,4,3,2,7] :=
  losing_excluded a [6,5,1,0,8,4,3,2,7] (by decide) b_1643 (by decide +kernel) 3 1 8 cert_1643 (by change 3 ≠ 1 ∧ ¬ edgeOf a b_1643 3 1 ∧ 8 ≠ 3 ∧ maskRegion 1210114499164850615222273 3 8; decide +kernel)

theorem node_1642 : Excluded a [6,5,1,0,8,4,3,2] :=
  branch_excluded a [6,5,1,0,8,4,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,1,0,8,4,3,2,0] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,3,2,1] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,3,2,3] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,3,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,3,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,3,2,6] (by decide +kernel))
      node_1643
      (invalid_excluded a [6,5,1,0,8,4,3,2,8] (by decide +kernel)))

theorem node_1641 : Excluded a [6,5,1,0,8,4,3] :=
  branch_excluded a [6,5,1,0,8,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,1,0,8,4,3,0] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,3,1] (by decide +kernel))
      node_1642
      (invalid_excluded a [6,5,1,0,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,3,8] (by decide +kernel)))

theorem node_1639 : Excluded a [6,5,1,0,8,4] :=
  branch_excluded a [6,5,1,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,1,0,8,4,0] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,1] (by decide +kernel))
      node_1640
      node_1641
      (invalid_excluded a [6,5,1,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,4,8] (by decide +kernel)))

theorem node_1644 : Excluded a [6,5,1,0,8,7] :=
  source_excluded a [6,5,1,0,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1636 : Excluded a [6,5,1,0,8] :=
  branch_excluded a [6,5,1,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,1,0,8,0] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,1] (by decide +kernel))
      node_1637
      node_1638
      node_1639
      (invalid_excluded a [6,5,1,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,8,6] (by decide +kernel))
      node_1644
      (invalid_excluded a [6,5,1,0,8,8] (by decide +kernel)))

theorem node_1620 : Excluded a [6,5,1,0] :=
  branch_excluded a [6,5,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,1,0,0] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,1] (by decide +kernel))
      node_1621
      node_1622
      (invalid_excluded a [6,5,1,0,4] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,0,6] (by decide +kernel))
      node_1631
      node_1636)

theorem node_1645 : Excluded a [6,5,1,2] :=
  predecessor_excluded a [6,5,1,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_1647 : Excluded a [6,5,1,7,0] :=
  predecessor_excluded a [6,5,1,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1648 : Excluded a [6,5,1,7,2] :=
  source_excluded a [6,5,1,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1650 : Excluded a [6,5,1,7,3,0] :=
  source_excluded a [6,5,1,7,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1651 : Excluded a [6,5,1,7,3,2] :=
  source_excluded a [6,5,1,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1652 : Excluded a [6,5,1,7,3,4] :=
  predecessor_excluded a [6,5,1,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1654 : Excluded a [6,5,1,7,3,8,0] :=
  predecessor_excluded a [6,5,1,7,3,8,0] 1 0 5 6 (by decide) (by decide +kernel)

theorem node_1655 : Excluded a [6,5,1,7,3,8,2] :=
  predecessor_excluded a [6,5,1,7,3,8,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1656 : Excluded a [6,5,1,7,3,8,4] :=
  source_excluded a [6,5,1,7,3,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1653 : Excluded a [6,5,1,7,3,8] :=
  branch_excluded a [6,5,1,7,3,8] (by decide)
    (fin9_cases _
      node_1654
      (invalid_excluded a [6,5,1,7,3,8,1] (by decide +kernel))
      node_1655
      (invalid_excluded a [6,5,1,7,3,8,3] (by decide +kernel))
      node_1656
      (invalid_excluded a [6,5,1,7,3,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,7,3,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,1,7,3,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,1,7,3,8,8] (by decide +kernel)))

theorem node_1649 : Excluded a [6,5,1,7,3] :=
  branch_excluded a [6,5,1,7,3] (by decide)
    (fin9_cases _
      node_1650
      (invalid_excluded a [6,5,1,7,3,1] (by decide +kernel))
      node_1651
      (invalid_excluded a [6,5,1,7,3,3] (by decide +kernel))
      node_1652
      (invalid_excluded a [6,5,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,1,7,3,7] (by decide +kernel))
      node_1653)

theorem node_1657 : Excluded a [6,5,1,7,8] :=
  predecessor_excluded a [6,5,1,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1646 : Excluded a [6,5,1,7] :=
  branch_excluded a [6,5,1,7] (by decide)
    (fin9_cases _
      node_1647
      (invalid_excluded a [6,5,1,7,1] (by decide +kernel))
      node_1648
      node_1649
      (invalid_excluded a [6,5,1,7,4] (by decide +kernel))
      (invalid_excluded a [6,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,1,7,7] (by decide +kernel))
      node_1657)

theorem node_1659 : Excluded a [6,5,1,8,0] :=
  predecessor_excluded a [6,5,1,8,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1660 : Excluded a [6,5,1,8,2] :=
  source_excluded a [6,5,1,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1662 : Excluded a [6,5,1,8,3,0] :=
  source_excluded a [6,5,1,8,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1663 : Excluded a [6,5,1,8,3,2] :=
  source_excluded a [6,5,1,8,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1664 : Excluded a [6,5,1,8,3,4] :=
  predecessor_excluded a [6,5,1,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1665 : Excluded a [6,5,1,8,3,7] :=
  source_excluded a [6,5,1,8,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1661 : Excluded a [6,5,1,8,3] :=
  branch_excluded a [6,5,1,8,3] (by decide)
    (fin9_cases _
      node_1662
      (invalid_excluded a [6,5,1,8,3,1] (by decide +kernel))
      node_1663
      (invalid_excluded a [6,5,1,8,3,3] (by decide +kernel))
      node_1664
      (invalid_excluded a [6,5,1,8,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,8,3,6] (by decide +kernel))
      node_1665
      (invalid_excluded a [6,5,1,8,3,8] (by decide +kernel)))

theorem node_1667 : Excluded a [6,5,1,8,7,0] :=
  source_excluded a [6,5,1,8,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1668 : Excluded a [6,5,1,8,7,2] :=
  source_excluded a [6,5,1,8,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1669 : Excluded a [6,5,1,8,7,3] :=
  predecessor_excluded a [6,5,1,8,7,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_1670 : Excluded a [6,5,1,8,7,4] :=
  predecessor_excluded a [6,5,1,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1666 : Excluded a [6,5,1,8,7] :=
  branch_excluded a [6,5,1,8,7] (by decide)
    (fin9_cases _
      node_1667
      (invalid_excluded a [6,5,1,8,7,1] (by decide +kernel))
      node_1668
      node_1669
      node_1670
      (invalid_excluded a [6,5,1,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,1,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,5,1,8,7,8] (by decide +kernel)))

theorem node_1658 : Excluded a [6,5,1,8] :=
  branch_excluded a [6,5,1,8] (by decide)
    (fin9_cases _
      node_1659
      (invalid_excluded a [6,5,1,8,1] (by decide +kernel))
      node_1660
      node_1661
      (invalid_excluded a [6,5,1,8,4] (by decide +kernel))
      (invalid_excluded a [6,5,1,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,8,6] (by decide +kernel))
      node_1666
      (invalid_excluded a [6,5,1,8,8] (by decide +kernel)))

theorem node_1619 : Excluded a [6,5,1] :=
  branch_excluded a [6,5,1] (by decide)
    (fin9_cases _
      node_1620
      (invalid_excluded a [6,5,1,1] (by decide +kernel))
      node_1645
      (invalid_excluded a [6,5,1,3] (by decide +kernel))
      (invalid_excluded a [6,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,5,1,6] (by decide +kernel))
      node_1646
      node_1658)

theorem node_1671 : Excluded a [6,5,4] :=
  source_excluded a [6,5,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1674 : Excluded a [6,5,7,0,1] :=
  source_excluded a [6,5,7,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1675 : Excluded a [6,5,7,0,2] :=
  source_excluded a [6,5,7,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1677 : Excluded a [6,5,7,0,3,1] :=
  source_excluded a [6,5,7,0,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1678 : Excluded a [6,5,7,0,3,2] :=
  source_excluded a [6,5,7,0,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1679 : Excluded a [6,5,7,0,3,4] :=
  predecessor_excluded a [6,5,7,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1681 : Excluded a [6,5,7,0,3,8,1] :=
  source_excluded a [6,5,7,0,3,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1682 : Excluded a [6,5,7,0,3,8,2] :=
  source_excluded a [6,5,7,0,3,8,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1685 : Excluded a [6,5,7,0,3,8,4,1,2] :=
  predecessor_excluded a [6,5,7,0,3,8,4,1,2] 0 2 7 8 (by decide) (by decide +kernel)

theorem node_1684 : Excluded a [6,5,7,0,3,8,4,1] :=
  branch_excluded a [6,5,7,0,3,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,3,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,1,1] (by decide +kernel))
      node_1685
      (invalid_excluded a [6,5,7,0,3,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,1,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,1,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,1,8] (by decide +kernel)))

theorem node_1687 : Excluded a [6,5,7,0,3,8,4,2,1] :=
  source_excluded a [6,5,7,0,3,8,4,2,1] 8 2 0 (by decide) (by decide +kernel)

theorem node_1686 : Excluded a [6,5,7,0,3,8,4,2] :=
  branch_excluded a [6,5,7,0,3,8,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,3,8,4,2,0] (by decide +kernel))
      node_1687
      (invalid_excluded a [6,5,7,0,3,8,4,2,2] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,2,3] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,2,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,2,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,2,8] (by decide +kernel)))

theorem node_1683 : Excluded a [6,5,7,0,3,8,4] :=
  branch_excluded a [6,5,7,0,3,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,3,8,4,0] (by decide +kernel))
      node_1684
      node_1686
      (invalid_excluded a [6,5,7,0,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,4,8] (by decide +kernel)))

theorem node_1680 : Excluded a [6,5,7,0,3,8] :=
  branch_excluded a [6,5,7,0,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,3,8,0] (by decide +kernel))
      node_1681
      node_1682
      (invalid_excluded a [6,5,7,0,3,8,3] (by decide +kernel))
      node_1683
      (invalid_excluded a [6,5,7,0,3,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,8,8] (by decide +kernel)))

theorem node_1676 : Excluded a [6,5,7,0,3] :=
  branch_excluded a [6,5,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,3,0] (by decide +kernel))
      node_1677
      node_1678
      (invalid_excluded a [6,5,7,0,3,3] (by decide +kernel))
      node_1679
      (invalid_excluded a [6,5,7,0,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,3,7] (by decide +kernel))
      node_1680)

theorem node_1689 : Excluded a [6,5,7,0,8,1] :=
  source_excluded a [6,5,7,0,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1690 : Excluded a [6,5,7,0,8,2] :=
  source_excluded a [6,5,7,0,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1691 : Excluded a [6,5,7,0,8,3] :=
  predecessor_excluded a [6,5,7,0,8,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_1693 : Excluded a [6,5,7,0,8,4,1] :=
  source_excluded a [6,5,7,0,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1694 : Excluded a [6,5,7,0,8,4,2] :=
  source_excluded a [6,5,7,0,8,4,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1695 : Excluded a [6,5,7,0,8,4,3] :=
  source_excluded a [6,5,7,0,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1692 : Excluded a [6,5,7,0,8,4] :=
  branch_excluded a [6,5,7,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,8,4,0] (by decide +kernel))
      node_1693
      node_1694
      node_1695
      (invalid_excluded a [6,5,7,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,4,8] (by decide +kernel)))

theorem node_1688 : Excluded a [6,5,7,0,8] :=
  branch_excluded a [6,5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,8,0] (by decide +kernel))
      node_1689
      node_1690
      node_1691
      node_1692
      (invalid_excluded a [6,5,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,8,8] (by decide +kernel)))

theorem node_1673 : Excluded a [6,5,7,0] :=
  branch_excluded a [6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,0,0] (by decide +kernel))
      node_1674
      node_1675
      node_1676
      (invalid_excluded a [6,5,7,0,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,0,7] (by decide +kernel))
      node_1688)

theorem node_1696 : Excluded a [6,5,7,1] :=
  predecessor_excluded a [6,5,7,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1698 : Excluded a [6,5,7,2,0] :=
  predecessor_excluded a [6,5,7,2,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1699 : Excluded a [6,5,7,2,1] :=
  source_excluded a [6,5,7,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1700 : Excluded a [6,5,7,2,3] :=
  predecessor_excluded a [6,5,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1702 : Excluded a [6,5,7,2,8,0] :=
  source_excluded a [6,5,7,2,8,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1703 : Excluded a [6,5,7,2,8,1] :=
  source_excluded a [6,5,7,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1704 : Excluded a [6,5,7,2,8,3] :=
  predecessor_excluded a [6,5,7,2,8,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_1707 : Excluded a [6,5,7,2,8,4,0,1] :=
  predecessor_excluded a [6,5,7,2,8,4,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_1708 : Excluded a [6,5,7,2,8,4,0,3] :=
  source_excluded a [6,5,7,2,8,4,0,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_1706 : Excluded a [6,5,7,2,8,4,0] :=
  branch_excluded a [6,5,7,2,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,5,7,2,8,4,0,0] (by decide +kernel))
      node_1707
      (invalid_excluded a [6,5,7,2,8,4,0,2] (by decide +kernel))
      node_1708
      (invalid_excluded a [6,5,7,2,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,0,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,0,8] (by decide +kernel)))

theorem node_1709 : Excluded a [6,5,7,2,8,4,1] :=
  source_excluded a [6,5,7,2,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1710 : Excluded a [6,5,7,2,8,4,3] :=
  source_excluded a [6,5,7,2,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1705 : Excluded a [6,5,7,2,8,4] :=
  branch_excluded a [6,5,7,2,8,4] (by decide)
    (fin9_cases _
      node_1706
      node_1709
      (invalid_excluded a [6,5,7,2,8,4,2] (by decide +kernel))
      node_1710
      (invalid_excluded a [6,5,7,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,4,8] (by decide +kernel)))

theorem node_1701 : Excluded a [6,5,7,2,8] :=
  branch_excluded a [6,5,7,2,8] (by decide)
    (fin9_cases _
      node_1702
      node_1703
      (invalid_excluded a [6,5,7,2,8,2] (by decide +kernel))
      node_1704
      node_1705
      (invalid_excluded a [6,5,7,2,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,8,8] (by decide +kernel)))

theorem node_1697 : Excluded a [6,5,7,2] :=
  branch_excluded a [6,5,7,2] (by decide)
    (fin9_cases _
      node_1698
      node_1699
      (invalid_excluded a [6,5,7,2,2] (by decide +kernel))
      node_1700
      (invalid_excluded a [6,5,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,2,7] (by decide +kernel))
      node_1701)

theorem node_1711 : Excluded a [6,5,7,8] :=
  predecessor_excluded a [6,5,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_1672 : Excluded a [6,5,7] :=
  branch_excluded a [6,5,7] (by decide)
    (fin9_cases _
      node_1673
      node_1696
      node_1697
      (invalid_excluded a [6,5,7,3] (by decide +kernel))
      (invalid_excluded a [6,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,7,7] (by decide +kernel))
      node_1711)

theorem node_1713 : Excluded a [6,5,8,0] :=
  predecessor_excluded a [6,5,8,0] 1 0 2 3 (by decide) (by decide +kernel)

theorem node_1714 : Excluded a [6,5,8,1] :=
  predecessor_excluded a [6,5,8,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_1716 : Excluded a [6,5,8,2,0] :=
  predecessor_excluded a [6,5,8,2,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1717 : Excluded a [6,5,8,2,1] :=
  source_excluded a [6,5,8,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1718 : Excluded a [6,5,8,2,3] :=
  predecessor_excluded a [6,5,8,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1720 : Excluded a [6,5,8,2,7,0] :=
  source_excluded a [6,5,8,2,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1721 : Excluded a [6,5,8,2,7,1] :=
  source_excluded a [6,5,8,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1722 : Excluded a [6,5,8,2,7,3] :=
  predecessor_excluded a [6,5,8,2,7,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_1723 : Excluded a [6,5,8,2,7,4] :=
  predecessor_excluded a [6,5,8,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1719 : Excluded a [6,5,8,2,7] :=
  branch_excluded a [6,5,8,2,7] (by decide)
    (fin9_cases _
      node_1720
      node_1721
      (invalid_excluded a [6,5,8,2,7,2] (by decide +kernel))
      node_1722
      node_1723
      (invalid_excluded a [6,5,8,2,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,7] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,7,8] (by decide +kernel)))

theorem node_1715 : Excluded a [6,5,8,2] :=
  branch_excluded a [6,5,8,2] (by decide)
    (fin9_cases _
      node_1716
      node_1717
      (invalid_excluded a [6,5,8,2,2] (by decide +kernel))
      node_1718
      (invalid_excluded a [6,5,8,2,4] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,2,6] (by decide +kernel))
      node_1719
      (invalid_excluded a [6,5,8,2,8] (by decide +kernel)))

theorem node_1725 : Excluded a [6,5,8,7,0] :=
  predecessor_excluded a [6,5,8,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1726 : Excluded a [6,5,8,7,1] :=
  source_excluded a [6,5,8,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1727 : Excluded a [6,5,8,7,2] :=
  source_excluded a [6,5,8,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_1729 : Excluded a [6,5,8,7,3,0] :=
  source_excluded a [6,5,8,7,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1730 : Excluded a [6,5,8,7,3,1] :=
  source_excluded a [6,5,8,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1731 : Excluded a [6,5,8,7,3,2] :=
  source_excluded a [6,5,8,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_1732 : Excluded a [6,5,8,7,3,4] :=
  predecessor_excluded a [6,5,8,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1728 : Excluded a [6,5,8,7,3] :=
  branch_excluded a [6,5,8,7,3] (by decide)
    (fin9_cases _
      node_1729
      node_1730
      node_1731
      (invalid_excluded a [6,5,8,7,3,3] (by decide +kernel))
      node_1732
      (invalid_excluded a [6,5,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,5,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,5,8,7,3,8] (by decide +kernel)))

theorem node_1724 : Excluded a [6,5,8,7] :=
  branch_excluded a [6,5,8,7] (by decide)
    (fin9_cases _
      node_1725
      node_1726
      node_1727
      node_1728
      (invalid_excluded a [6,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,5,8,7,8] (by decide +kernel)))

theorem node_1712 : Excluded a [6,5,8] :=
  branch_excluded a [6,5,8] (by decide)
    (fin9_cases _
      node_1713
      node_1714
      node_1715
      (invalid_excluded a [6,5,8,3] (by decide +kernel))
      (invalid_excluded a [6,5,8,4] (by decide +kernel))
      (invalid_excluded a [6,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,5,8,6] (by decide +kernel))
      node_1724
      (invalid_excluded a [6,5,8,8] (by decide +kernel)))

theorem node_1574 : Excluded a [6,5] :=
  branch_excluded a [6,5] (by decide)
    (fin9_cases _
      node_1575
      node_1619
      (invalid_excluded a [6,5,2] (by decide +kernel))
      (invalid_excluded a [6,5,3] (by decide +kernel))
      node_1671
      (invalid_excluded a [6,5,5] (by decide +kernel))
      (invalid_excluded a [6,5,6] (by decide +kernel))
      node_1672
      node_1712)

theorem node_1733 : Excluded a [6,7] :=
  predecessor_excluded a [6,7] 2 7 0 1 (by decide) (by decide +kernel)

theorem node_1735 : Excluded a [6,8,0] :=
  predecessor_excluded a [6,8,0] 3 0 1 2 (by decide) (by decide +kernel)

theorem node_1739 : Excluded a [6,8,1,0,2,3] :=
  predecessor_excluded a [6,8,1,0,2,3] 0 3 4 5 (by decide) (by decide +kernel)

def b_1743 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 4
  | 6 => 3
  | 7 => 5
  | 8 => 7
  | _ => 0

def cert_1743 : LosingRegion (edgeOf a b_1743) 0 :=
  losingMask a b_1743 0 1212487268136607131108352
    (by decide +kernel) (by decide +kernel)

theorem node_1743 : Excluded a [6,8,1,0,2,4,3,5,7] :=
  losing_excluded a [6,8,1,0,2,4,3,5,7] (by decide) b_1743 (by decide +kernel) 4 0 1 cert_1743 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_1743 4 0 ∧ 1 ≠ 4 ∧ maskRegion 1212487268136607131108352 4 1; decide +kernel)

theorem node_1742 : Excluded a [6,8,1,0,2,4,3,5] :=
  branch_excluded a [6,8,1,0,2,4,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,0,2,4,3,5,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,3,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,3,5,3] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,3,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,3,5,6] (by decide +kernel))
      node_1743
      (invalid_excluded a [6,8,1,0,2,4,3,5,8] (by decide +kernel)))

theorem node_1741 : Excluded a [6,8,1,0,2,4,3] :=
  branch_excluded a [6,8,1,0,2,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,0,2,4,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,3,4] (by decide +kernel))
      node_1742
      (invalid_excluded a [6,8,1,0,2,4,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,3,8] (by decide +kernel)))

theorem node_1744 : Excluded a [6,8,1,0,2,4,5] :=
  predecessor_excluded a [6,8,1,0,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1740 : Excluded a [6,8,1,0,2,4] :=
  branch_excluded a [6,8,1,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,0,2,4,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,2] (by decide +kernel))
      node_1741
      (invalid_excluded a [6,8,1,0,2,4,4] (by decide +kernel))
      node_1744
      (invalid_excluded a [6,8,1,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,4,8] (by decide +kernel)))

theorem node_1745 : Excluded a [6,8,1,0,2,7] :=
  source_excluded a [6,8,1,0,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1738 : Excluded a [6,8,1,0,2] :=
  branch_excluded a [6,8,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,2] (by decide +kernel))
      node_1739
      node_1740
      (invalid_excluded a [6,8,1,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,2,6] (by decide +kernel))
      node_1745
      (invalid_excluded a [6,8,1,0,2,8] (by decide +kernel)))

theorem node_1749 : Excluded a [6,8,1,0,3,2,4,5] :=
  predecessor_excluded a [6,8,1,0,3,2,4,5] 0 5 6 7 (by decide) (by decide +kernel)

theorem node_1748 : Excluded a [6,8,1,0,3,2,4] :=
  branch_excluded a [6,8,1,0,3,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,0,3,2,4,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,4,2] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,4,3] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,4,4] (by decide +kernel))
      node_1749
      (invalid_excluded a [6,8,1,0,3,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,4,8] (by decide +kernel)))

def b_1752 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
  | 6 => 5
  | 7 => 4
  | 8 => 7
  | _ => 0

def cert_1752 : LosingRegion (edgeOf a b_1752) 0 :=
  losingMask a b_1752 0 1210126138340096072483840
    (by decide +kernel) (by decide +kernel)

theorem node_1752 : Excluded a [6,8,1,0,3,2,5,4,7] :=
  losing_excluded a [6,8,1,0,3,2,5,4,7] (by decide) b_1752 (by decide +kernel) 4 0 2 cert_1752 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_1752 4 0 ∧ 2 ≠ 4 ∧ maskRegion 1210126138340096072483840 4 2; decide +kernel)

theorem node_1751 : Excluded a [6,8,1,0,3,2,5,4] :=
  branch_excluded a [6,8,1,0,3,2,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,0,3,2,5,4,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,5,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,5,4,2] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,5,4,3] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,5,4,6] (by decide +kernel))
      node_1752
      (invalid_excluded a [6,8,1,0,3,2,5,4,8] (by decide +kernel)))

theorem node_1750 : Excluded a [6,8,1,0,3,2,5] :=
  branch_excluded a [6,8,1,0,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,0,3,2,5,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,5,3] (by decide +kernel))
      node_1751
      (invalid_excluded a [6,8,1,0,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,5,8] (by decide +kernel)))

theorem node_1747 : Excluded a [6,8,1,0,3,2] :=
  branch_excluded a [6,8,1,0,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,0,3,2,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,3] (by decide +kernel))
      node_1748
      node_1750
      (invalid_excluded a [6,8,1,0,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,2,8] (by decide +kernel)))

theorem node_1753 : Excluded a [6,8,1,0,3,4] :=
  predecessor_excluded a [6,8,1,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1754 : Excluded a [6,8,1,0,3,7] :=
  source_excluded a [6,8,1,0,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1746 : Excluded a [6,8,1,0,3] :=
  branch_excluded a [6,8,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,1] (by decide +kernel))
      node_1747
      (invalid_excluded a [6,8,1,0,3,3] (by decide +kernel))
      node_1753
      (invalid_excluded a [6,8,1,0,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,3,6] (by decide +kernel))
      node_1754
      (invalid_excluded a [6,8,1,0,3,8] (by decide +kernel)))

theorem node_1757 : Excluded a [6,8,1,0,7,2,3] :=
  predecessor_excluded a [6,8,1,0,7,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_1758 : Excluded a [6,8,1,0,7,2,4] :=
  source_excluded a [6,8,1,0,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1759 : Excluded a [6,8,1,0,7,2,5] :=
  source_excluded a [6,8,1,0,7,2,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1756 : Excluded a [6,8,1,0,7,2] :=
  branch_excluded a [6,8,1,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,0,7,2,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,7,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,7,2,2] (by decide +kernel))
      node_1757
      node_1758
      node_1759
      (invalid_excluded a [6,8,1,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,7,2,8] (by decide +kernel)))

theorem node_1761 : Excluded a [6,8,1,0,7,3,2] :=
  predecessor_excluded a [6,8,1,0,7,3,2] 3 2 0 6 (by decide) (by decide +kernel)

theorem node_1762 : Excluded a [6,8,1,0,7,3,4] :=
  source_excluded a [6,8,1,0,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1763 : Excluded a [6,8,1,0,7,3,5] :=
  source_excluded a [6,8,1,0,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1760 : Excluded a [6,8,1,0,7,3] :=
  branch_excluded a [6,8,1,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,0,7,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,7,3,1] (by decide +kernel))
      node_1761
      (invalid_excluded a [6,8,1,0,7,3,3] (by decide +kernel))
      node_1762
      node_1763
      (invalid_excluded a [6,8,1,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,7,3,8] (by decide +kernel)))

theorem node_1764 : Excluded a [6,8,1,0,7,4] :=
  predecessor_excluded a [6,8,1,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1755 : Excluded a [6,8,1,0,7] :=
  branch_excluded a [6,8,1,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,0,7,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,7,1] (by decide +kernel))
      node_1756
      node_1760
      node_1764
      (invalid_excluded a [6,8,1,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,7,8] (by decide +kernel)))

theorem node_1737 : Excluded a [6,8,1,0] :=
  branch_excluded a [6,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,1] (by decide +kernel))
      node_1738
      node_1746
      (invalid_excluded a [6,8,1,0,4] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,0,6] (by decide +kernel))
      node_1755
      (invalid_excluded a [6,8,1,0,8] (by decide +kernel)))

theorem node_1765 : Excluded a [6,8,1,2] :=
  predecessor_excluded a [6,8,1,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_1766 : Excluded a [6,8,1,5] :=
  source_excluded a [6,8,1,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1768 : Excluded a [6,8,1,7,0] :=
  predecessor_excluded a [6,8,1,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1770 : Excluded a [6,8,1,7,2,0] :=
  source_excluded a [6,8,1,7,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1771 : Excluded a [6,8,1,7,2,3] :=
  predecessor_excluded a [6,8,1,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1775 : Excluded a [6,8,1,7,2,4,0,3,5] :=
  predecessor_excluded a [6,8,1,7,2,4,0,3,5] 1 6 8 0 (by decide) (by decide +kernel)

theorem node_1774 : Excluded a [6,8,1,7,2,4,0,3] :=
  branch_excluded a [6,8,1,7,2,4,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,7,2,4,0,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,0,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,0,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,0,3,3] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,0,3,4] (by decide +kernel))
      node_1775
      (invalid_excluded a [6,8,1,7,2,4,0,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,0,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,0,3,8] (by decide +kernel)))

theorem node_1776 : Excluded a [6,8,1,7,2,4,0,5] :=
  predecessor_excluded a [6,8,1,7,2,4,0,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_1773 : Excluded a [6,8,1,7,2,4,0] :=
  branch_excluded a [6,8,1,7,2,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,7,2,4,0,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,0,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,0,2] (by decide +kernel))
      node_1774
      (invalid_excluded a [6,8,1,7,2,4,0,4] (by decide +kernel))
      node_1776
      (invalid_excluded a [6,8,1,7,2,4,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,0,8] (by decide +kernel)))

theorem node_1777 : Excluded a [6,8,1,7,2,4,3] :=
  source_excluded a [6,8,1,7,2,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1778 : Excluded a [6,8,1,7,2,4,5] :=
  predecessor_excluded a [6,8,1,7,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1772 : Excluded a [6,8,1,7,2,4] :=
  branch_excluded a [6,8,1,7,2,4] (by decide)
    (fin9_cases _
      node_1773
      (invalid_excluded a [6,8,1,7,2,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,2] (by decide +kernel))
      node_1777
      (invalid_excluded a [6,8,1,7,2,4,4] (by decide +kernel))
      node_1778
      (invalid_excluded a [6,8,1,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,8] (by decide +kernel)))

theorem node_1769 : Excluded a [6,8,1,7,2] :=
  branch_excluded a [6,8,1,7,2] (by decide)
    (fin9_cases _
      node_1770
      (invalid_excluded a [6,8,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,2] (by decide +kernel))
      node_1771
      node_1772
      (invalid_excluded a [6,8,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,8] (by decide +kernel)))

theorem node_1780 : Excluded a [6,8,1,7,3,0] :=
  source_excluded a [6,8,1,7,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1783 : Excluded a [6,8,1,7,3,2,0,4] :=
  source_excluded a [6,8,1,7,3,2,0,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_1784 : Excluded a [6,8,1,7,3,2,0,5] :=
  predecessor_excluded a [6,8,1,7,3,2,0,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_1782 : Excluded a [6,8,1,7,3,2,0] :=
  branch_excluded a [6,8,1,7,3,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,1,7,3,2,0,0] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,0,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,0,2] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,0,3] (by decide +kernel))
      node_1783
      node_1784
      (invalid_excluded a [6,8,1,7,3,2,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,0,8] (by decide +kernel)))

theorem node_1785 : Excluded a [6,8,1,7,3,2,4] :=
  source_excluded a [6,8,1,7,3,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1787 : Excluded a [6,8,1,7,3,2,5,0] :=
  source_excluded a [6,8,1,7,3,2,5,0] 7 1 8 (by decide) (by decide +kernel)

theorem node_1788 : Excluded a [6,8,1,7,3,2,5,4] :=
  source_excluded a [6,8,1,7,3,2,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_1786 : Excluded a [6,8,1,7,3,2,5] :=
  branch_excluded a [6,8,1,7,3,2,5] (by decide)
    (fin9_cases _
      node_1787
      (invalid_excluded a [6,8,1,7,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,5,3] (by decide +kernel))
      node_1788
      (invalid_excluded a [6,8,1,7,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,5,8] (by decide +kernel)))

theorem node_1781 : Excluded a [6,8,1,7,3,2] :=
  branch_excluded a [6,8,1,7,3,2] (by decide)
    (fin9_cases _
      node_1782
      (invalid_excluded a [6,8,1,7,3,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,3] (by decide +kernel))
      node_1785
      node_1786
      (invalid_excluded a [6,8,1,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,8] (by decide +kernel)))

theorem node_1789 : Excluded a [6,8,1,7,3,4] :=
  predecessor_excluded a [6,8,1,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1779 : Excluded a [6,8,1,7,3] :=
  branch_excluded a [6,8,1,7,3] (by decide)
    (fin9_cases _
      node_1780
      (invalid_excluded a [6,8,1,7,3,1] (by decide +kernel))
      node_1781
      (invalid_excluded a [6,8,1,7,3,3] (by decide +kernel))
      node_1789
      (invalid_excluded a [6,8,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,8] (by decide +kernel)))

theorem node_1767 : Excluded a [6,8,1,7] :=
  branch_excluded a [6,8,1,7] (by decide)
    (fin9_cases _
      node_1768
      (invalid_excluded a [6,8,1,7,1] (by decide +kernel))
      node_1769
      node_1779
      (invalid_excluded a [6,8,1,7,4] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,8] (by decide +kernel)))

theorem node_1736 : Excluded a [6,8,1] :=
  branch_excluded a [6,8,1] (by decide)
    (fin9_cases _
      node_1737
      (invalid_excluded a [6,8,1,1] (by decide +kernel))
      node_1765
      (invalid_excluded a [6,8,1,3] (by decide +kernel))
      (invalid_excluded a [6,8,1,4] (by decide +kernel))
      node_1766
      (invalid_excluded a [6,8,1,6] (by decide +kernel))
      node_1767
      (invalid_excluded a [6,8,1,8] (by decide +kernel)))

theorem node_1790 : Excluded a [6,8,4] :=
  source_excluded a [6,8,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1793 : Excluded a [6,8,5,0,1] :=
  predecessor_excluded a [6,8,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1794 : Excluded a [6,8,5,0,2] :=
  source_excluded a [6,8,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1795 : Excluded a [6,8,5,0,3] :=
  source_excluded a [6,8,5,0,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1797 : Excluded a [6,8,5,0,7,1] :=
  source_excluded a [6,8,5,0,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1799 : Excluded a [6,8,5,0,7,2,1] :=
  source_excluded a [6,8,5,0,7,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1800 : Excluded a [6,8,5,0,7,2,3] :=
  predecessor_excluded a [6,8,5,0,7,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_1801 : Excluded a [6,8,5,0,7,2,4] :=
  source_excluded a [6,8,5,0,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1798 : Excluded a [6,8,5,0,7,2] :=
  branch_excluded a [6,8,5,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,0,7,2,0] (by decide +kernel))
      node_1799
      (invalid_excluded a [6,8,5,0,7,2,2] (by decide +kernel))
      node_1800
      node_1801
      (invalid_excluded a [6,8,5,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,2,8] (by decide +kernel)))

theorem node_1802 : Excluded a [6,8,5,0,7,3] :=
  source_excluded a [6,8,5,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1803 : Excluded a [6,8,5,0,7,4] :=
  predecessor_excluded a [6,8,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1796 : Excluded a [6,8,5,0,7] :=
  branch_excluded a [6,8,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,0,7,0] (by decide +kernel))
      node_1797
      node_1798
      node_1802
      node_1803
      (invalid_excluded a [6,8,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,8] (by decide +kernel)))

theorem node_1792 : Excluded a [6,8,5,0] :=
  branch_excluded a [6,8,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,0,0] (by decide +kernel))
      node_1793
      node_1794
      node_1795
      (invalid_excluded a [6,8,5,0,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,6] (by decide +kernel))
      node_1796
      (invalid_excluded a [6,8,5,0,8] (by decide +kernel)))

theorem node_1805 : Excluded a [6,8,5,1,0] :=
  predecessor_excluded a [6,8,5,1,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1806 : Excluded a [6,8,5,1,2] :=
  source_excluded a [6,8,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1807 : Excluded a [6,8,5,1,3] :=
  source_excluded a [6,8,5,1,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1809 : Excluded a [6,8,5,1,7,0] :=
  source_excluded a [6,8,5,1,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1813 : Excluded a [6,8,5,1,7,2,0,3,4] :=
  predecessor_excluded a [6,8,5,1,7,2,0,3,4] 0 4 7 8 (by decide) (by decide +kernel)

theorem node_1812 : Excluded a [6,8,5,1,7,2,0,3] :=
  branch_excluded a [6,8,5,1,7,2,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,1,7,2,0,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,3,3] (by decide +kernel))
      node_1813
      (invalid_excluded a [6,8,5,1,7,2,0,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,3,8] (by decide +kernel)))

theorem node_1815 : Excluded a [6,8,5,1,7,2,0,4,3] :=
  predecessor_excluded a [6,8,5,1,7,2,0,4,3] 2 1 8 3 (by decide) (by decide +kernel)

theorem node_1814 : Excluded a [6,8,5,1,7,2,0,4] :=
  branch_excluded a [6,8,5,1,7,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,1,7,2,0,4,0] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,4,2] (by decide +kernel))
      node_1815
      (invalid_excluded a [6,8,5,1,7,2,0,4,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,4,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,4,8] (by decide +kernel)))

theorem node_1811 : Excluded a [6,8,5,1,7,2,0] :=
  branch_excluded a [6,8,5,1,7,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,1,7,2,0,0] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,1] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,2] (by decide +kernel))
      node_1812
      node_1814
      (invalid_excluded a [6,8,5,1,7,2,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,0,8] (by decide +kernel)))

theorem node_1816 : Excluded a [6,8,5,1,7,2,3] :=
  predecessor_excluded a [6,8,5,1,7,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_1817 : Excluded a [6,8,5,1,7,2,4] :=
  source_excluded a [6,8,5,1,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1810 : Excluded a [6,8,5,1,7,2] :=
  branch_excluded a [6,8,5,1,7,2] (by decide)
    (fin9_cases _
      node_1811
      (invalid_excluded a [6,8,5,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,2] (by decide +kernel))
      node_1816
      node_1817
      (invalid_excluded a [6,8,5,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,8] (by decide +kernel)))

theorem node_1818 : Excluded a [6,8,5,1,7,3] :=
  source_excluded a [6,8,5,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1819 : Excluded a [6,8,5,1,7,4] :=
  predecessor_excluded a [6,8,5,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1808 : Excluded a [6,8,5,1,7] :=
  branch_excluded a [6,8,5,1,7] (by decide)
    (fin9_cases _
      node_1809
      (invalid_excluded a [6,8,5,1,7,1] (by decide +kernel))
      node_1810
      node_1818
      node_1819
      (invalid_excluded a [6,8,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,8] (by decide +kernel)))

theorem node_1804 : Excluded a [6,8,5,1] :=
  branch_excluded a [6,8,5,1] (by decide)
    (fin9_cases _
      node_1805
      (invalid_excluded a [6,8,5,1,1] (by decide +kernel))
      node_1806
      node_1807
      (invalid_excluded a [6,8,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,6] (by decide +kernel))
      node_1808
      (invalid_excluded a [6,8,5,1,8] (by decide +kernel)))

theorem node_1820 : Excluded a [6,8,5,2] :=
  predecessor_excluded a [6,8,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_1822 : Excluded a [6,8,5,7,0] :=
  predecessor_excluded a [6,8,5,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1824 : Excluded a [6,8,5,7,1,0] :=
  source_excluded a [6,8,5,7,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1825 : Excluded a [6,8,5,7,1,2] :=
  predecessor_excluded a [6,8,5,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1826 : Excluded a [6,8,5,7,1,3] :=
  source_excluded a [6,8,5,7,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1827 : Excluded a [6,8,5,7,1,4] :=
  predecessor_excluded a [6,8,5,7,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_1823 : Excluded a [6,8,5,7,1] :=
  branch_excluded a [6,8,5,7,1] (by decide)
    (fin9_cases _
      node_1824
      (invalid_excluded a [6,8,5,7,1,1] (by decide +kernel))
      node_1825
      node_1826
      node_1827
      (invalid_excluded a [6,8,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,8] (by decide +kernel)))

theorem node_1828 : Excluded a [6,8,5,7,2] :=
  source_excluded a [6,8,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1829 : Excluded a [6,8,5,7,3] :=
  source_excluded a [6,8,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1821 : Excluded a [6,8,5,7] :=
  branch_excluded a [6,8,5,7] (by decide)
    (fin9_cases _
      node_1822
      node_1823
      node_1828
      node_1829
      (invalid_excluded a [6,8,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,8] (by decide +kernel)))

theorem node_1791 : Excluded a [6,8,5] :=
  branch_excluded a [6,8,5] (by decide)
    (fin9_cases _
      node_1792
      node_1804
      node_1820
      (invalid_excluded a [6,8,5,3] (by decide +kernel))
      (invalid_excluded a [6,8,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,6] (by decide +kernel))
      node_1821
      (invalid_excluded a [6,8,5,8] (by decide +kernel)))

theorem node_1832 : Excluded a [6,8,7,0,1] :=
  predecessor_excluded a [6,8,7,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1834 : Excluded a [6,8,7,0,2,1] :=
  source_excluded a [6,8,7,0,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1835 : Excluded a [6,8,7,0,2,3] :=
  predecessor_excluded a [6,8,7,0,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_1837 : Excluded a [6,8,7,0,2,4,1] :=
  source_excluded a [6,8,7,0,2,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1838 : Excluded a [6,8,7,0,2,4,3] :=
  source_excluded a [6,8,7,0,2,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1839 : Excluded a [6,8,7,0,2,4,5] :=
  predecessor_excluded a [6,8,7,0,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1836 : Excluded a [6,8,7,0,2,4] :=
  branch_excluded a [6,8,7,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,4,0] (by decide +kernel))
      node_1837
      (invalid_excluded a [6,8,7,0,2,4,2] (by decide +kernel))
      node_1838
      (invalid_excluded a [6,8,7,0,2,4,4] (by decide +kernel))
      node_1839
      (invalid_excluded a [6,8,7,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,8] (by decide +kernel)))

theorem node_1833 : Excluded a [6,8,7,0,2] :=
  branch_excluded a [6,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,0] (by decide +kernel))
      node_1834
      (invalid_excluded a [6,8,7,0,2,2] (by decide +kernel))
      node_1835
      node_1836
      (invalid_excluded a [6,8,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,8] (by decide +kernel)))

theorem node_1841 : Excluded a [6,8,7,0,3,1] :=
  source_excluded a [6,8,7,0,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1842 : Excluded a [6,8,7,0,3,2] :=
  predecessor_excluded a [6,8,7,0,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1843 : Excluded a [6,8,7,0,3,4] :=
  predecessor_excluded a [6,8,7,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1840 : Excluded a [6,8,7,0,3] :=
  branch_excluded a [6,8,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,3,0] (by decide +kernel))
      node_1841
      node_1842
      (invalid_excluded a [6,8,7,0,3,3] (by decide +kernel))
      node_1843
      (invalid_excluded a [6,8,7,0,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,3,8] (by decide +kernel)))

theorem node_1831 : Excluded a [6,8,7,0] :=
  branch_excluded a [6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,0] (by decide +kernel))
      node_1832
      node_1833
      node_1840
      (invalid_excluded a [6,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,8] (by decide +kernel)))

theorem node_1845 : Excluded a [6,8,7,1,0] :=
  predecessor_excluded a [6,8,7,1,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1846 : Excluded a [6,8,7,1,2] :=
  predecessor_excluded a [6,8,7,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1848 : Excluded a [6,8,7,1,3,0] :=
  source_excluded a [6,8,7,1,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1849 : Excluded a [6,8,7,1,3,2] :=
  predecessor_excluded a [6,8,7,1,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1850 : Excluded a [6,8,7,1,3,4] :=
  predecessor_excluded a [6,8,7,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1847 : Excluded a [6,8,7,1,3] :=
  branch_excluded a [6,8,7,1,3] (by decide)
    (fin9_cases _
      node_1848
      (invalid_excluded a [6,8,7,1,3,1] (by decide +kernel))
      node_1849
      (invalid_excluded a [6,8,7,1,3,3] (by decide +kernel))
      node_1850
      (invalid_excluded a [6,8,7,1,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,3,8] (by decide +kernel)))

theorem node_1844 : Excluded a [6,8,7,1] :=
  branch_excluded a [6,8,7,1] (by decide)
    (fin9_cases _
      node_1845
      (invalid_excluded a [6,8,7,1,1] (by decide +kernel))
      node_1846
      node_1847
      (invalid_excluded a [6,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,8] (by decide +kernel)))

theorem node_1852 : Excluded a [6,8,7,2,0] :=
  predecessor_excluded a [6,8,7,2,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1854 : Excluded a [6,8,7,2,1,0] :=
  source_excluded a [6,8,7,2,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1857 : Excluded a [6,8,7,2,1,3,0,4] :=
  predecessor_excluded a [6,8,7,2,1,3,0,4] 0 4 2 7 (by decide) (by decide +kernel)

theorem node_1859 : Excluded a [6,8,7,2,1,3,0,5,4] :=
  predecessor_excluded a [6,8,7,2,1,3,0,5,4] 2 1 8 4 (by decide) (by decide +kernel)

theorem node_1858 : Excluded a [6,8,7,2,1,3,0,5] :=
  branch_excluded a [6,8,7,2,1,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,2,1,3,0,5,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,0,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,0,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,0,5,3] (by decide +kernel))
      node_1859
      (invalid_excluded a [6,8,7,2,1,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,0,5,8] (by decide +kernel)))

theorem node_1856 : Excluded a [6,8,7,2,1,3,0] :=
  branch_excluded a [6,8,7,2,1,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,2,1,3,0,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,0,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,0,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,0,3] (by decide +kernel))
      node_1857
      node_1858
      (invalid_excluded a [6,8,7,2,1,3,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,0,8] (by decide +kernel)))

theorem node_1860 : Excluded a [6,8,7,2,1,3,4] :=
  predecessor_excluded a [6,8,7,2,1,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_1862 : Excluded a [6,8,7,2,1,3,5,0] :=
  source_excluded a [6,8,7,2,1,3,5,0] 7 1 8 (by decide) (by decide +kernel)

theorem node_1863 : Excluded a [6,8,7,2,1,3,5,4] :=
  predecessor_excluded a [6,8,7,2,1,3,5,4] 0 4 2 7 (by decide) (by decide +kernel)

theorem node_1861 : Excluded a [6,8,7,2,1,3,5] :=
  branch_excluded a [6,8,7,2,1,3,5] (by decide)
    (fin9_cases _
      node_1862
      (invalid_excluded a [6,8,7,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,3] (by decide +kernel))
      node_1863
      (invalid_excluded a [6,8,7,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,8] (by decide +kernel)))

theorem node_1855 : Excluded a [6,8,7,2,1,3] :=
  branch_excluded a [6,8,7,2,1,3] (by decide)
    (fin9_cases _
      node_1856
      (invalid_excluded a [6,8,7,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,3] (by decide +kernel))
      node_1860
      node_1861
      (invalid_excluded a [6,8,7,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,8] (by decide +kernel)))

theorem node_1866 : Excluded a [6,8,7,2,1,4,0,3] :=
  source_excluded a [6,8,7,2,1,4,0,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_1868 : Excluded a [6,8,7,2,1,4,0,5,3] :=
  predecessor_excluded a [6,8,7,2,1,4,0,5,3] 0 3 1 8 (by decide) (by decide +kernel)

theorem node_1867 : Excluded a [6,8,7,2,1,4,0,5] :=
  branch_excluded a [6,8,7,2,1,4,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,2,1,4,0,5,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,0,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,0,5,2] (by decide +kernel))
      node_1868
      (invalid_excluded a [6,8,7,2,1,4,0,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,0,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,0,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,0,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,0,5,8] (by decide +kernel)))

theorem node_1865 : Excluded a [6,8,7,2,1,4,0] :=
  branch_excluded a [6,8,7,2,1,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,2,1,4,0,0] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,0,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,0,2] (by decide +kernel))
      node_1866
      (invalid_excluded a [6,8,7,2,1,4,0,4] (by decide +kernel))
      node_1867
      (invalid_excluded a [6,8,7,2,1,4,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,0,8] (by decide +kernel)))

theorem node_1869 : Excluded a [6,8,7,2,1,4,3] :=
  source_excluded a [6,8,7,2,1,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1870 : Excluded a [6,8,7,2,1,4,5] :=
  predecessor_excluded a [6,8,7,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1864 : Excluded a [6,8,7,2,1,4] :=
  branch_excluded a [6,8,7,2,1,4] (by decide)
    (fin9_cases _
      node_1865
      (invalid_excluded a [6,8,7,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,2] (by decide +kernel))
      node_1869
      (invalid_excluded a [6,8,7,2,1,4,4] (by decide +kernel))
      node_1870
      (invalid_excluded a [6,8,7,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,8] (by decide +kernel)))

theorem node_1853 : Excluded a [6,8,7,2,1] :=
  branch_excluded a [6,8,7,2,1] (by decide)
    (fin9_cases _
      node_1854
      (invalid_excluded a [6,8,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,2] (by decide +kernel))
      node_1855
      node_1864
      (invalid_excluded a [6,8,7,2,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,8] (by decide +kernel)))

theorem node_1871 : Excluded a [6,8,7,2,3] :=
  predecessor_excluded a [6,8,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1851 : Excluded a [6,8,7,2] :=
  branch_excluded a [6,8,7,2] (by decide)
    (fin9_cases _
      node_1852
      node_1853
      (invalid_excluded a [6,8,7,2,2] (by decide +kernel))
      node_1871
      (invalid_excluded a [6,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,8] (by decide +kernel)))

theorem node_1872 : Excluded a [6,8,7,5] :=
  source_excluded a [6,8,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1830 : Excluded a [6,8,7] :=
  branch_excluded a [6,8,7] (by decide)
    (fin9_cases _
      node_1831
      node_1844
      node_1851
      (invalid_excluded a [6,8,7,3] (by decide +kernel))
      (invalid_excluded a [6,8,7,4] (by decide +kernel))
      node_1872
      (invalid_excluded a [6,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,8] (by decide +kernel)))

theorem node_1734 : Excluded a [6,8] :=
  branch_excluded a [6,8] (by decide)
    (fin9_cases _
      node_1735
      node_1736
      (invalid_excluded a [6,8,2] (by decide +kernel))
      (invalid_excluded a [6,8,3] (by decide +kernel))
      node_1790
      node_1791
      (invalid_excluded a [6,8,6] (by decide +kernel))
      node_1830
      (invalid_excluded a [6,8,8] (by decide +kernel)))

theorem node_1324 : Excluded a [6] :=
  branch_excluded a [6] (by decide)
    (fin9_cases _
      node_1325
      (invalid_excluded a [6,1] (by decide +kernel))
      (invalid_excluded a [6,2] (by decide +kernel))
      node_1502
      node_1503
      node_1574
      (invalid_excluded a [6,6] (by decide +kernel))
      node_1733
      node_1734)

theorem node_1875 : Excluded a [7,0,1] :=
  predecessor_excluded a [7,0,1] 3 1 1 2 (by decide) (by decide +kernel)

theorem node_1876 : Excluded a [7,0,4] :=
  source_excluded a [7,0,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1879 : Excluded a [7,0,5,1,2] :=
  source_excluded a [7,0,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1880 : Excluded a [7,0,5,1,3] :=
  source_excluded a [7,0,5,1,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1881 : Excluded a [7,0,5,1,6] :=
  source_excluded a [7,0,5,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1884 : Excluded a [7,0,5,1,8,2,3] :=
  predecessor_excluded a [7,0,5,1,8,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_1885 : Excluded a [7,0,5,1,8,2,4] :=
  predecessor_excluded a [7,0,5,1,8,2,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1883 : Excluded a [7,0,5,1,8,2] :=
  branch_excluded a [7,0,5,1,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,5,1,8,2,0] (by decide +kernel))
      (invalid_excluded a [7,0,5,1,8,2,1] (by decide +kernel))
      (invalid_excluded a [7,0,5,1,8,2,2] (by decide +kernel))
      node_1884
      node_1885
      (invalid_excluded a [7,0,5,1,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,0,5,1,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,0,5,1,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,0,5,1,8,2,8] (by decide +kernel)))

theorem node_1886 : Excluded a [7,0,5,1,8,3] :=
  source_excluded a [7,0,5,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1887 : Excluded a [7,0,5,1,8,4] :=
  predecessor_excluded a [7,0,5,1,8,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_1882 : Excluded a [7,0,5,1,8] :=
  branch_excluded a [7,0,5,1,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,5,1,8,0] (by decide +kernel))
      (invalid_excluded a [7,0,5,1,8,1] (by decide +kernel))
      node_1883
      node_1886
      node_1887
      (invalid_excluded a [7,0,5,1,8,5] (by decide +kernel))
      (invalid_excluded a [7,0,5,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,0,5,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,0,5,1,8,8] (by decide +kernel)))

theorem node_1878 : Excluded a [7,0,5,1] :=
  branch_excluded a [7,0,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,5,1,0] (by decide +kernel))
      (invalid_excluded a [7,0,5,1,1] (by decide +kernel))
      node_1879
      node_1880
      (invalid_excluded a [7,0,5,1,4] (by decide +kernel))
      (invalid_excluded a [7,0,5,1,5] (by decide +kernel))
      node_1881
      (invalid_excluded a [7,0,5,1,7] (by decide +kernel))
      node_1882)

theorem node_1888 : Excluded a [7,0,5,2] :=
  predecessor_excluded a [7,0,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_1889 : Excluded a [7,0,5,6] :=
  predecessor_excluded a [7,0,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_1892 : Excluded a [7,0,5,8,1,2] :=
  predecessor_excluded a [7,0,5,8,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1893 : Excluded a [7,0,5,8,1,3] :=
  source_excluded a [7,0,5,8,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1894 : Excluded a [7,0,5,8,1,4] :=
  predecessor_excluded a [7,0,5,8,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_1891 : Excluded a [7,0,5,8,1] :=
  branch_excluded a [7,0,5,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,5,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,0,5,8,1,1] (by decide +kernel))
      node_1892
      node_1893
      node_1894
      (invalid_excluded a [7,0,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,0,5,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,0,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,0,5,8,1,8] (by decide +kernel)))

theorem node_1895 : Excluded a [7,0,5,8,2] :=
  source_excluded a [7,0,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1896 : Excluded a [7,0,5,8,3] :=
  source_excluded a [7,0,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1897 : Excluded a [7,0,5,8,6] :=
  source_excluded a [7,0,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1890 : Excluded a [7,0,5,8] :=
  branch_excluded a [7,0,5,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,5,8,0] (by decide +kernel))
      node_1891
      node_1895
      node_1896
      (invalid_excluded a [7,0,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,0,5,8,5] (by decide +kernel))
      node_1897
      (invalid_excluded a [7,0,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,0,5,8,8] (by decide +kernel)))

theorem node_1877 : Excluded a [7,0,5] :=
  branch_excluded a [7,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,5,0] (by decide +kernel))
      node_1878
      node_1888
      (invalid_excluded a [7,0,5,3] (by decide +kernel))
      (invalid_excluded a [7,0,5,4] (by decide +kernel))
      (invalid_excluded a [7,0,5,5] (by decide +kernel))
      node_1889
      (invalid_excluded a [7,0,5,7] (by decide +kernel))
      node_1890)

theorem node_1900 : Excluded a [7,0,6,1,2] :=
  predecessor_excluded a [7,0,6,1,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_1902 : Excluded a [7,0,6,1,3,2] :=
  source_excluded a [7,0,6,1,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1903 : Excluded a [7,0,6,1,3,4] :=
  predecessor_excluded a [7,0,6,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1907 : Excluded a [7,0,6,1,3,8,2,4,5] :=
  predecessor_excluded a [7,0,6,1,3,8,2,4,5] 0 5 7 8 (by decide) (by decide +kernel)

theorem node_1906 : Excluded a [7,0,6,1,3,8,2,4] :=
  branch_excluded a [7,0,6,1,3,8,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,1,3,8,2,4,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,8,2,4,1] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,8,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,8,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,8,2,4,4] (by decide +kernel))
      node_1907
      (invalid_excluded a [7,0,6,1,3,8,2,4,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,8,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,8,2,4,8] (by decide +kernel)))

theorem node_1908 : Excluded a [7,0,6,1,3,8,2,5] :=
  source_excluded a [7,0,6,1,3,8,2,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_1905 : Excluded a [7,0,6,1,3,8,2] :=
  branch_excluded a [7,0,6,1,3,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,1,3,8,2,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,8,2,1] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,8,2,2] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,8,2,3] (by decide +kernel))
      node_1906
      node_1908
      (invalid_excluded a [7,0,6,1,3,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,8,2,8] (by decide +kernel)))

theorem node_1909 : Excluded a [7,0,6,1,3,8,4] :=
  predecessor_excluded a [7,0,6,1,3,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_1910 : Excluded a [7,0,6,1,3,8,5] :=
  predecessor_excluded a [7,0,6,1,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_1904 : Excluded a [7,0,6,1,3,8] :=
  branch_excluded a [7,0,6,1,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,1,3,8,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,8,1] (by decide +kernel))
      node_1905
      (invalid_excluded a [7,0,6,1,3,8,3] (by decide +kernel))
      node_1909
      node_1910
      (invalid_excluded a [7,0,6,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,8,8] (by decide +kernel)))

theorem node_1901 : Excluded a [7,0,6,1,3] :=
  branch_excluded a [7,0,6,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,1] (by decide +kernel))
      node_1902
      (invalid_excluded a [7,0,6,1,3,3] (by decide +kernel))
      node_1903
      (invalid_excluded a [7,0,6,1,3,5] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,3,7] (by decide +kernel))
      node_1904)

theorem node_1912 : Excluded a [7,0,6,1,8,2] :=
  source_excluded a [7,0,6,1,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1913 : Excluded a [7,0,6,1,8,3] :=
  source_excluded a [7,0,6,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1916 : Excluded a [7,0,6,1,8,4,2,3] :=
  predecessor_excluded a [7,0,6,1,8,4,2,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_1917 : Excluded a [7,0,6,1,8,4,2,5] :=
  source_excluded a [7,0,6,1,8,4,2,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_1915 : Excluded a [7,0,6,1,8,4,2] :=
  branch_excluded a [7,0,6,1,8,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,1,8,4,2,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,8,4,2,1] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,8,4,2,2] (by decide +kernel))
      node_1916
      (invalid_excluded a [7,0,6,1,8,4,2,4] (by decide +kernel))
      node_1917
      (invalid_excluded a [7,0,6,1,8,4,2,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,8,4,2,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,8,4,2,8] (by decide +kernel)))

theorem node_1918 : Excluded a [7,0,6,1,8,4,3] :=
  source_excluded a [7,0,6,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1919 : Excluded a [7,0,6,1,8,4,5] :=
  predecessor_excluded a [7,0,6,1,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1914 : Excluded a [7,0,6,1,8,4] :=
  branch_excluded a [7,0,6,1,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,1,8,4,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,8,4,1] (by decide +kernel))
      node_1915
      node_1918
      (invalid_excluded a [7,0,6,1,8,4,4] (by decide +kernel))
      node_1919
      (invalid_excluded a [7,0,6,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,8,4,8] (by decide +kernel)))

theorem node_1911 : Excluded a [7,0,6,1,8] :=
  branch_excluded a [7,0,6,1,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,1,8,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,8,1] (by decide +kernel))
      node_1912
      node_1913
      node_1914
      (invalid_excluded a [7,0,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,8,8] (by decide +kernel)))

theorem node_1899 : Excluded a [7,0,6,1] :=
  branch_excluded a [7,0,6,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,1,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,1] (by decide +kernel))
      node_1900
      node_1901
      (invalid_excluded a [7,0,6,1,4] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,1,7] (by decide +kernel))
      node_1911)

theorem node_1922 : Excluded a [7,0,6,2,1,3] :=
  source_excluded a [7,0,6,2,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1924 : Excluded a [7,0,6,2,1,4,3] :=
  source_excluded a [7,0,6,2,1,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1925 : Excluded a [7,0,6,2,1,4,5] :=
  predecessor_excluded a [7,0,6,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1926 : Excluded a [7,0,6,2,1,4,8] :=
  source_excluded a [7,0,6,2,1,4,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_1923 : Excluded a [7,0,6,2,1,4] :=
  branch_excluded a [7,0,6,2,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,2,1,4,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,1,4,2] (by decide +kernel))
      node_1924
      (invalid_excluded a [7,0,6,2,1,4,4] (by decide +kernel))
      node_1925
      (invalid_excluded a [7,0,6,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,1,4,7] (by decide +kernel))
      node_1926)

theorem node_1928 : Excluded a [7,0,6,2,1,8,3] :=
  source_excluded a [7,0,6,2,1,8,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1929 : Excluded a [7,0,6,2,1,8,4] :=
  predecessor_excluded a [7,0,6,2,1,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_1930 : Excluded a [7,0,6,2,1,8,5] :=
  predecessor_excluded a [7,0,6,2,1,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_1927 : Excluded a [7,0,6,2,1,8] :=
  branch_excluded a [7,0,6,2,1,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,2,1,8,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,1,8,1] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,1,8,2] (by decide +kernel))
      node_1928
      node_1929
      node_1930
      (invalid_excluded a [7,0,6,2,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,1,8,8] (by decide +kernel)))

theorem node_1921 : Excluded a [7,0,6,2,1] :=
  branch_excluded a [7,0,6,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,2,1,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,1,2] (by decide +kernel))
      node_1922
      node_1923
      (invalid_excluded a [7,0,6,2,1,5] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,1,7] (by decide +kernel))
      node_1927)

theorem node_1931 : Excluded a [7,0,6,2,3] :=
  predecessor_excluded a [7,0,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1934 : Excluded a [7,0,6,2,8,1,3] :=
  source_excluded a [7,0,6,2,8,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1935 : Excluded a [7,0,6,2,8,1,4] :=
  predecessor_excluded a [7,0,6,2,8,1,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1938 : Excluded a [7,0,6,2,8,1,5,3,4] :=
  predecessor_excluded a [7,0,6,2,8,1,5,3,4] 0 4 7 8 (by decide) (by decide +kernel)

theorem node_1937 : Excluded a [7,0,6,2,8,1,5,3] :=
  branch_excluded a [7,0,6,2,8,1,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,2,8,1,5,3,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,5,3,1] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,5,3,2] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,5,3,3] (by decide +kernel))
      node_1938
      (invalid_excluded a [7,0,6,2,8,1,5,3,5] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,5,3,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,5,3,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,5,3,8] (by decide +kernel)))

theorem node_1939 : Excluded a [7,0,6,2,8,1,5,4] :=
  source_excluded a [7,0,6,2,8,1,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_1936 : Excluded a [7,0,6,2,8,1,5] :=
  branch_excluded a [7,0,6,2,8,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,2,8,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,5,1] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,5,2] (by decide +kernel))
      node_1937
      node_1939
      (invalid_excluded a [7,0,6,2,8,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,5,8] (by decide +kernel)))

theorem node_1933 : Excluded a [7,0,6,2,8,1] :=
  branch_excluded a [7,0,6,2,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,2,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,2] (by decide +kernel))
      node_1934
      node_1935
      node_1936
      (invalid_excluded a [7,0,6,2,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,1,8] (by decide +kernel)))

theorem node_1940 : Excluded a [7,0,6,2,8,3] :=
  source_excluded a [7,0,6,2,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1942 : Excluded a [7,0,6,2,8,4,1] :=
  source_excluded a [7,0,6,2,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1943 : Excluded a [7,0,6,2,8,4,3] :=
  source_excluded a [7,0,6,2,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1944 : Excluded a [7,0,6,2,8,4,5] :=
  predecessor_excluded a [7,0,6,2,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1941 : Excluded a [7,0,6,2,8,4] :=
  branch_excluded a [7,0,6,2,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,2,8,4,0] (by decide +kernel))
      node_1942
      (invalid_excluded a [7,0,6,2,8,4,2] (by decide +kernel))
      node_1943
      (invalid_excluded a [7,0,6,2,8,4,4] (by decide +kernel))
      node_1944
      (invalid_excluded a [7,0,6,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,4,8] (by decide +kernel)))

theorem node_1932 : Excluded a [7,0,6,2,8] :=
  branch_excluded a [7,0,6,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,2,8,0] (by decide +kernel))
      node_1933
      (invalid_excluded a [7,0,6,2,8,2] (by decide +kernel))
      node_1940
      node_1941
      (invalid_excluded a [7,0,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,8,8] (by decide +kernel)))

theorem node_1920 : Excluded a [7,0,6,2] :=
  branch_excluded a [7,0,6,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,2,0] (by decide +kernel))
      node_1921
      (invalid_excluded a [7,0,6,2,2] (by decide +kernel))
      node_1931
      (invalid_excluded a [7,0,6,2,4] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,5] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,2,7] (by decide +kernel))
      node_1932)

theorem node_1945 : Excluded a [7,0,6,5] :=
  source_excluded a [7,0,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1948 : Excluded a [7,0,6,8,1,2] :=
  source_excluded a [7,0,6,8,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1949 : Excluded a [7,0,6,8,1,3] :=
  source_excluded a [7,0,6,8,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1952 : Excluded a [7,0,6,8,1,4,2,3] :=
  source_excluded a [7,0,6,8,1,4,2,3] 7 0 3 (by decide) (by decide +kernel)

def b_1954 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 0
  | 2 => 6
  | 3 => 8
  | 4 => 1
  | 5 => 4
  | 6 => 2
  | 7 => 5
  | 8 => 3
  | _ => 0

def cert_1954 : LosingRegion (edgeOf a b_1954) 0 :=
  losingMask a b_1954 0 1212549696612257579926528
    (by decide +kernel) (by decide +kernel)

theorem node_1954 : Excluded a [7,0,6,8,1,4,2,5,3] :=
  losing_excluded a [7,0,6,8,1,4,2,5,3] (by decide) b_1954 (by decide +kernel) 2 0 3 cert_1954 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1954 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1212549696612257579926528 2 3; decide +kernel)

theorem node_1953 : Excluded a [7,0,6,8,1,4,2,5] :=
  branch_excluded a [7,0,6,8,1,4,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,8,1,4,2,5,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,4,2,5,1] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,4,2,5,2] (by decide +kernel))
      node_1954
      (invalid_excluded a [7,0,6,8,1,4,2,5,4] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,4,2,5,5] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,4,2,5,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,4,2,5,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,4,2,5,8] (by decide +kernel)))

theorem node_1951 : Excluded a [7,0,6,8,1,4,2] :=
  branch_excluded a [7,0,6,8,1,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,8,1,4,2,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,4,2,1] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,4,2,2] (by decide +kernel))
      node_1952
      (invalid_excluded a [7,0,6,8,1,4,2,4] (by decide +kernel))
      node_1953
      (invalid_excluded a [7,0,6,8,1,4,2,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,4,2,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,4,2,8] (by decide +kernel)))

theorem node_1955 : Excluded a [7,0,6,8,1,4,3] :=
  source_excluded a [7,0,6,8,1,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1956 : Excluded a [7,0,6,8,1,4,5] :=
  predecessor_excluded a [7,0,6,8,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1950 : Excluded a [7,0,6,8,1,4] :=
  branch_excluded a [7,0,6,8,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,8,1,4,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,4,1] (by decide +kernel))
      node_1951
      node_1955
      (invalid_excluded a [7,0,6,8,1,4,4] (by decide +kernel))
      node_1956
      (invalid_excluded a [7,0,6,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,4,8] (by decide +kernel)))

theorem node_1947 : Excluded a [7,0,6,8,1] :=
  branch_excluded a [7,0,6,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,1] (by decide +kernel))
      node_1948
      node_1949
      node_1950
      (invalid_excluded a [7,0,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,1,8] (by decide +kernel)))

theorem node_1957 : Excluded a [7,0,6,8,2] :=
  predecessor_excluded a [7,0,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_1960 : Excluded a [7,0,6,8,3,1,2] :=
  predecessor_excluded a [7,0,6,8,3,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_1961 : Excluded a [7,0,6,8,3,1,4] :=
  predecessor_excluded a [7,0,6,8,3,1,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_1963 : Excluded a [7,0,6,8,3,1,5,2] :=
  predecessor_excluded a [7,0,6,8,3,1,5,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_1964 : Excluded a [7,0,6,8,3,1,5,4] :=
  source_excluded a [7,0,6,8,3,1,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_1962 : Excluded a [7,0,6,8,3,1,5] :=
  branch_excluded a [7,0,6,8,3,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,8,3,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,3,1,5,1] (by decide +kernel))
      node_1963
      (invalid_excluded a [7,0,6,8,3,1,5,3] (by decide +kernel))
      node_1964
      (invalid_excluded a [7,0,6,8,3,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,3,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,3,1,5,8] (by decide +kernel)))

theorem node_1959 : Excluded a [7,0,6,8,3,1] :=
  branch_excluded a [7,0,6,8,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,8,3,1,0] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,3,1,1] (by decide +kernel))
      node_1960
      (invalid_excluded a [7,0,6,8,3,1,3] (by decide +kernel))
      node_1961
      node_1962
      (invalid_excluded a [7,0,6,8,3,1,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,3,1,8] (by decide +kernel)))

theorem node_1965 : Excluded a [7,0,6,8,3,2] :=
  source_excluded a [7,0,6,8,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1966 : Excluded a [7,0,6,8,3,4] :=
  predecessor_excluded a [7,0,6,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1958 : Excluded a [7,0,6,8,3] :=
  branch_excluded a [7,0,6,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,8,3,0] (by decide +kernel))
      node_1959
      node_1965
      (invalid_excluded a [7,0,6,8,3,3] (by decide +kernel))
      node_1966
      (invalid_excluded a [7,0,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,3,8] (by decide +kernel)))

theorem node_1946 : Excluded a [7,0,6,8] :=
  branch_excluded a [7,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,8,0] (by decide +kernel))
      node_1947
      node_1957
      node_1958
      (invalid_excluded a [7,0,6,8,4] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,0,6,8,8] (by decide +kernel)))

theorem node_1898 : Excluded a [7,0,6] :=
  branch_excluded a [7,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,6,0] (by decide +kernel))
      node_1899
      node_1920
      (invalid_excluded a [7,0,6,3] (by decide +kernel))
      (invalid_excluded a [7,0,6,4] (by decide +kernel))
      node_1945
      (invalid_excluded a [7,0,6,6] (by decide +kernel))
      (invalid_excluded a [7,0,6,7] (by decide +kernel))
      node_1946)

theorem node_1969 : Excluded a [7,0,8,1,2] :=
  predecessor_excluded a [7,0,8,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1973 : Excluded a [7,0,8,1,3,2,4,5] :=
  predecessor_excluded a [7,0,8,1,3,2,4,5] 0 5 6 7 (by decide) (by decide +kernel)

def b_1975 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 0
  | 2 => 8
  | 3 => 1
  | 4 => 3
  | 5 => 2
  | 6 => 4
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_1975 : LosingRegion (edgeOf a b_1975) 0 :=
  losingMask a b_1975 0 1212513275844532001309696
    (by decide +kernel) (by decide +kernel)

theorem node_1975 : Excluded a [7,0,8,1,3,2,4,6,5] :=
  losing_excluded a [7,0,8,1,3,2,4,6,5] (by decide) b_1975 (by decide +kernel) 2 0 8 cert_1975 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1975 2 0 ∧ 8 ≠ 2 ∧ maskRegion 1212513275844532001309696 2 8; decide +kernel)

theorem node_1974 : Excluded a [7,0,8,1,3,2,4,6] :=
  branch_excluded a [7,0,8,1,3,2,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,1,3,2,4,6,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,4,6,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,4,6,4] (by decide +kernel))
      node_1975
      (invalid_excluded a [7,0,8,1,3,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,4,6,8] (by decide +kernel)))

theorem node_1972 : Excluded a [7,0,8,1,3,2,4] :=
  branch_excluded a [7,0,8,1,3,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,1,3,2,4,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,4,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,4,4] (by decide +kernel))
      node_1973
      node_1974
      (invalid_excluded a [7,0,8,1,3,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,4,8] (by decide +kernel)))

theorem node_1978 : Excluded a [7,0,8,1,3,2,5,4,6] :=
  predecessor_excluded a [7,0,8,1,3,2,5,4,6] 1 7 8 0 (by decide) (by decide +kernel)

theorem node_1977 : Excluded a [7,0,8,1,3,2,5,4] :=
  branch_excluded a [7,0,8,1,3,2,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,1,3,2,5,4,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,5,4,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,5,4,2] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,5,4,3] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,5,4,5] (by decide +kernel))
      node_1978
      (invalid_excluded a [7,0,8,1,3,2,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,5,4,8] (by decide +kernel)))

theorem node_1979 : Excluded a [7,0,8,1,3,2,5,6] :=
  predecessor_excluded a [7,0,8,1,3,2,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_1976 : Excluded a [7,0,8,1,3,2,5] :=
  branch_excluded a [7,0,8,1,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,1,3,2,5,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,5,3] (by decide +kernel))
      node_1977
      (invalid_excluded a [7,0,8,1,3,2,5,5] (by decide +kernel))
      node_1979
      (invalid_excluded a [7,0,8,1,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,5,8] (by decide +kernel)))

theorem node_1971 : Excluded a [7,0,8,1,3,2] :=
  branch_excluded a [7,0,8,1,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,1,3,2,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,2] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,3] (by decide +kernel))
      node_1972
      node_1976
      (invalid_excluded a [7,0,8,1,3,2,6] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,2,8] (by decide +kernel)))

theorem node_1980 : Excluded a [7,0,8,1,3,4] :=
  predecessor_excluded a [7,0,8,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1970 : Excluded a [7,0,8,1,3] :=
  branch_excluded a [7,0,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,1] (by decide +kernel))
      node_1971
      (invalid_excluded a [7,0,8,1,3,3] (by decide +kernel))
      node_1980
      (invalid_excluded a [7,0,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,3,8] (by decide +kernel)))

theorem node_1981 : Excluded a [7,0,8,1,6] :=
  source_excluded a [7,0,8,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1968 : Excluded a [7,0,8,1] :=
  branch_excluded a [7,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,1] (by decide +kernel))
      node_1969
      node_1970
      (invalid_excluded a [7,0,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,5] (by decide +kernel))
      node_1981
      (invalid_excluded a [7,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,1,8] (by decide +kernel)))

theorem node_1985 : Excluded a [7,0,8,2,1,3,4] :=
  predecessor_excluded a [7,0,8,2,1,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_1988 : Excluded a [7,0,8,2,1,3,5,4,6] :=
  predecessor_excluded a [7,0,8,2,1,3,5,4,6] 1 7 8 0 (by decide) (by decide +kernel)

theorem node_1987 : Excluded a [7,0,8,2,1,3,5,4] :=
  branch_excluded a [7,0,8,2,1,3,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,2,1,3,5,4,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,5,4,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,5,4,2] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,5,4,3] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,5,4,5] (by decide +kernel))
      node_1988
      (invalid_excluded a [7,0,8,2,1,3,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,5,4,8] (by decide +kernel)))

theorem node_1989 : Excluded a [7,0,8,2,1,3,5,6] :=
  predecessor_excluded a [7,0,8,2,1,3,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_1986 : Excluded a [7,0,8,2,1,3,5] :=
  branch_excluded a [7,0,8,2,1,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,2,1,3,5,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,5,3] (by decide +kernel))
      node_1987
      (invalid_excluded a [7,0,8,2,1,3,5,5] (by decide +kernel))
      node_1989
      (invalid_excluded a [7,0,8,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,5,8] (by decide +kernel)))

theorem node_1984 : Excluded a [7,0,8,2,1,3] :=
  branch_excluded a [7,0,8,2,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,2,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,3] (by decide +kernel))
      node_1985
      node_1986
      (invalid_excluded a [7,0,8,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,3,8] (by decide +kernel)))

theorem node_1993 : Excluded a [7,0,8,2,1,4,3,5,6] :=
  predecessor_excluded a [7,0,8,2,1,4,3,5,6] 1 7 8 0 (by decide) (by decide +kernel)

theorem node_1992 : Excluded a [7,0,8,2,1,4,3,5] :=
  branch_excluded a [7,0,8,2,1,4,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,2,1,4,3,5,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,5,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,5,3] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,5,4] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,5,5] (by decide +kernel))
      node_1993
      (invalid_excluded a [7,0,8,2,1,4,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,5,8] (by decide +kernel)))

def b_1995 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 0
  | 2 => 8
  | 3 => 2
  | 4 => 1
  | 5 => 4
  | 6 => 3
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_1995 : LosingRegion (edgeOf a b_1995) 0 :=
  losingMask a b_1995 0 1212512839715857533764608
    (by decide +kernel) (by decide +kernel)

theorem node_1995 : Excluded a [7,0,8,2,1,4,3,6,5] :=
  losing_excluded a [7,0,8,2,1,4,3,6,5] (by decide) b_1995 (by decide +kernel) 2 0 7 cert_1995 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1995 2 0 ∧ 7 ≠ 2 ∧ maskRegion 1212512839715857533764608 2 7; decide +kernel)

theorem node_1994 : Excluded a [7,0,8,2,1,4,3,6] :=
  branch_excluded a [7,0,8,2,1,4,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,2,1,4,3,6,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,6,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,6,2] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,6,4] (by decide +kernel))
      node_1995
      (invalid_excluded a [7,0,8,2,1,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,6,8] (by decide +kernel)))

theorem node_1991 : Excluded a [7,0,8,2,1,4,3] :=
  branch_excluded a [7,0,8,2,1,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,2,1,4,3,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,2] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,4] (by decide +kernel))
      node_1992
      node_1994
      (invalid_excluded a [7,0,8,2,1,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,3,8] (by decide +kernel)))

theorem node_1996 : Excluded a [7,0,8,2,1,4,5] :=
  predecessor_excluded a [7,0,8,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_1990 : Excluded a [7,0,8,2,1,4] :=
  branch_excluded a [7,0,8,2,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,2,1,4,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,2] (by decide +kernel))
      node_1991
      (invalid_excluded a [7,0,8,2,1,4,4] (by decide +kernel))
      node_1996
      (invalid_excluded a [7,0,8,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,4,8] (by decide +kernel)))

theorem node_1983 : Excluded a [7,0,8,2,1] :=
  branch_excluded a [7,0,8,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,2,1,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,2] (by decide +kernel))
      node_1984
      node_1990
      (invalid_excluded a [7,0,8,2,1,5] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,6] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,1,8] (by decide +kernel)))

theorem node_1997 : Excluded a [7,0,8,2,3] :=
  predecessor_excluded a [7,0,8,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1998 : Excluded a [7,0,8,2,6] :=
  source_excluded a [7,0,8,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1982 : Excluded a [7,0,8,2] :=
  branch_excluded a [7,0,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,2,0] (by decide +kernel))
      node_1983
      (invalid_excluded a [7,0,8,2,2] (by decide +kernel))
      node_1997
      (invalid_excluded a [7,0,8,2,4] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,5] (by decide +kernel))
      node_1998
      (invalid_excluded a [7,0,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,2,8] (by decide +kernel)))

theorem node_1999 : Excluded a [7,0,8,5] :=
  source_excluded a [7,0,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2002 : Excluded a [7,0,8,6,1,2] :=
  predecessor_excluded a [7,0,8,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2003 : Excluded a [7,0,8,6,1,3] :=
  source_excluded a [7,0,8,6,1,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2004 : Excluded a [7,0,8,6,1,4] :=
  source_excluded a [7,0,8,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2001 : Excluded a [7,0,8,6,1] :=
  branch_excluded a [7,0,8,6,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,6,1,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,1,1] (by decide +kernel))
      node_2002
      node_2003
      node_2004
      (invalid_excluded a [7,0,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,1,8] (by decide +kernel)))

theorem node_2008 : Excluded a [7,0,8,6,2,1,3,4] :=
  predecessor_excluded a [7,0,8,6,2,1,3,4] 0 4 6 7 (by decide) (by decide +kernel)

theorem node_2010 : Excluded a [7,0,8,6,2,1,3,5,4] :=
  predecessor_excluded a [7,0,8,6,2,1,3,5,4] 0 4 2 8 (by decide) (by decide +kernel)

theorem node_2009 : Excluded a [7,0,8,6,2,1,3,5] :=
  branch_excluded a [7,0,8,6,2,1,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,6,2,1,3,5,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,3,5,3] (by decide +kernel))
      node_2010
      (invalid_excluded a [7,0,8,6,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,3,5,8] (by decide +kernel)))

theorem node_2007 : Excluded a [7,0,8,6,2,1,3] :=
  branch_excluded a [7,0,8,6,2,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,6,2,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,3,3] (by decide +kernel))
      node_2008
      node_2009
      (invalid_excluded a [7,0,8,6,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,3,8] (by decide +kernel)))

theorem node_2011 : Excluded a [7,0,8,6,2,1,4] :=
  source_excluded a [7,0,8,6,2,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2012 : Excluded a [7,0,8,6,2,1,5] :=
  predecessor_excluded a [7,0,8,6,2,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2006 : Excluded a [7,0,8,6,2,1] :=
  branch_excluded a [7,0,8,6,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,6,2,1,0] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,2] (by decide +kernel))
      node_2007
      node_2011
      node_2012
      (invalid_excluded a [7,0,8,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,1,8] (by decide +kernel)))

theorem node_2013 : Excluded a [7,0,8,6,2,3] :=
  source_excluded a [7,0,8,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2014 : Excluded a [7,0,8,6,2,4] :=
  source_excluded a [7,0,8,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2005 : Excluded a [7,0,8,6,2] :=
  branch_excluded a [7,0,8,6,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,6,2,0] (by decide +kernel))
      node_2006
      (invalid_excluded a [7,0,8,6,2,2] (by decide +kernel))
      node_2013
      node_2014
      (invalid_excluded a [7,0,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,6] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,2,8] (by decide +kernel)))

theorem node_2015 : Excluded a [7,0,8,6,3] :=
  predecessor_excluded a [7,0,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2000 : Excluded a [7,0,8,6] :=
  branch_excluded a [7,0,8,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,6,0] (by decide +kernel))
      node_2001
      node_2005
      node_2015
      (invalid_excluded a [7,0,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,6,8] (by decide +kernel)))

theorem node_1967 : Excluded a [7,0,8] :=
  branch_excluded a [7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,8,0] (by decide +kernel))
      node_1968
      node_1982
      (invalid_excluded a [7,0,8,3] (by decide +kernel))
      (invalid_excluded a [7,0,8,4] (by decide +kernel))
      node_1999
      node_2000
      (invalid_excluded a [7,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,0,8,8] (by decide +kernel)))

theorem node_1874 : Excluded a [7,0] :=
  branch_excluded a [7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0,0] (by decide +kernel))
      node_1875
      (invalid_excluded a [7,0,2] (by decide +kernel))
      (invalid_excluded a [7,0,3] (by decide +kernel))
      node_1876
      node_1877
      node_1898
      (invalid_excluded a [7,0,7] (by decide +kernel))
      node_1967)

theorem node_2016 : Excluded a [7,3] :=
  source_excluded a [7,3] 1 0 2 (by decide) (by decide +kernel)

theorem node_2019 : Excluded a [7,4,0,1] :=
  source_excluded a [7,4,0,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2020 : Excluded a [7,4,0,2] :=
  source_excluded a [7,4,0,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_2021 : Excluded a [7,4,0,5] :=
  source_excluded a [7,4,0,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2024 : Excluded a [7,4,0,6,1,2] :=
  predecessor_excluded a [7,4,0,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2025 : Excluded a [7,4,0,6,1,3] :=
  source_excluded a [7,4,0,6,1,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2028 : Excluded a [7,4,0,6,1,8,2,3] :=
  predecessor_excluded a [7,4,0,6,1,8,2,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_2029 : Excluded a [7,4,0,6,1,8,2,5] :=
  source_excluded a [7,4,0,6,1,8,2,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_2027 : Excluded a [7,4,0,6,1,8,2] :=
  branch_excluded a [7,4,0,6,1,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,1,8,2,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,8,2,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,8,2,2] (by decide +kernel))
      node_2028
      (invalid_excluded a [7,4,0,6,1,8,2,4] (by decide +kernel))
      node_2029
      (invalid_excluded a [7,4,0,6,1,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,8,2,8] (by decide +kernel)))

theorem node_2031 : Excluded a [7,4,0,6,1,8,3,2] :=
  predecessor_excluded a [7,4,0,6,1,8,3,2] 1 0 7 2 (by decide) (by decide +kernel)

theorem node_2032 : Excluded a [7,4,0,6,1,8,3,5] :=
  source_excluded a [7,4,0,6,1,8,3,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_2030 : Excluded a [7,4,0,6,1,8,3] :=
  branch_excluded a [7,4,0,6,1,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,1,8,3,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,8,3,1] (by decide +kernel))
      node_2031
      (invalid_excluded a [7,4,0,6,1,8,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,8,3,4] (by decide +kernel))
      node_2032
      (invalid_excluded a [7,4,0,6,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,8,3,8] (by decide +kernel)))

theorem node_2033 : Excluded a [7,4,0,6,1,8,5] :=
  predecessor_excluded a [7,4,0,6,1,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_2026 : Excluded a [7,4,0,6,1,8] :=
  branch_excluded a [7,4,0,6,1,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,1,8,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,8,1] (by decide +kernel))
      node_2027
      node_2030
      (invalid_excluded a [7,4,0,6,1,8,4] (by decide +kernel))
      node_2033
      (invalid_excluded a [7,4,0,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,8,8] (by decide +kernel)))

theorem node_2023 : Excluded a [7,4,0,6,1] :=
  branch_excluded a [7,4,0,6,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,1,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,1] (by decide +kernel))
      node_2024
      node_2025
      (invalid_excluded a [7,4,0,6,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,1,7] (by decide +kernel))
      node_2026)

theorem node_2034 : Excluded a [7,4,0,6,2] :=
  source_excluded a [7,4,0,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2035 : Excluded a [7,4,0,6,3] :=
  predecessor_excluded a [7,4,0,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2038 : Excluded a [7,4,0,6,8,1,2] :=
  predecessor_excluded a [7,4,0,6,8,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2040 : Excluded a [7,4,0,6,8,1,3,2] :=
  predecessor_excluded a [7,4,0,6,8,1,3,2] 1 0 7 2 (by decide) (by decide +kernel)

theorem node_2041 : Excluded a [7,4,0,6,8,1,3,5] :=
  source_excluded a [7,4,0,6,8,1,3,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_2039 : Excluded a [7,4,0,6,8,1,3] :=
  branch_excluded a [7,4,0,6,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,3,1] (by decide +kernel))
      node_2040
      (invalid_excluded a [7,4,0,6,8,1,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,3,4] (by decide +kernel))
      node_2041
      (invalid_excluded a [7,4,0,6,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,3,8] (by decide +kernel)))

theorem node_2042 : Excluded a [7,4,0,6,8,1,5] :=
  predecessor_excluded a [7,4,0,6,8,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2037 : Excluded a [7,4,0,6,8,1] :=
  branch_excluded a [7,4,0,6,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,1] (by decide +kernel))
      node_2038
      node_2039
      (invalid_excluded a [7,4,0,6,8,1,4] (by decide +kernel))
      node_2042
      (invalid_excluded a [7,4,0,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,8] (by decide +kernel)))

theorem node_2044 : Excluded a [7,4,0,6,8,2,1] :=
  source_excluded a [7,4,0,6,8,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2045 : Excluded a [7,4,0,6,8,2,3] :=
  predecessor_excluded a [7,4,0,6,8,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_2046 : Excluded a [7,4,0,6,8,2,5] :=
  predecessor_excluded a [7,4,0,6,8,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2043 : Excluded a [7,4,0,6,8,2] :=
  branch_excluded a [7,4,0,6,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,2,0] (by decide +kernel))
      node_2044
      (invalid_excluded a [7,4,0,6,8,2,2] (by decide +kernel))
      node_2045
      (invalid_excluded a [7,4,0,6,8,2,4] (by decide +kernel))
      node_2046
      (invalid_excluded a [7,4,0,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,2,8] (by decide +kernel)))

theorem node_2047 : Excluded a [7,4,0,6,8,3] :=
  source_excluded a [7,4,0,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2036 : Excluded a [7,4,0,6,8] :=
  branch_excluded a [7,4,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,0] (by decide +kernel))
      node_2037
      node_2043
      node_2047
      (invalid_excluded a [7,4,0,6,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,8] (by decide +kernel)))

theorem node_2022 : Excluded a [7,4,0,6] :=
  branch_excluded a [7,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,0] (by decide +kernel))
      node_2023
      node_2034
      node_2035
      (invalid_excluded a [7,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,7] (by decide +kernel))
      node_2036)

theorem node_2050 : Excluded a [7,4,0,8,1,2] :=
  predecessor_excluded a [7,4,0,8,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2054 : Excluded a [7,4,0,8,1,3,2,5,6] :=
  predecessor_excluded a [7,4,0,8,1,3,2,5,6] 1 7 8 0 (by decide) (by decide +kernel)

theorem node_2053 : Excluded a [7,4,0,8,1,3,2,5] :=
  branch_excluded a [7,4,0,8,1,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,1,3,2,5,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,5,5] (by decide +kernel))
      node_2054
      (invalid_excluded a [7,4,0,8,1,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,5,8] (by decide +kernel)))

theorem node_2056 : Excluded a [7,4,0,8,1,3,2,6,5] :=
  predecessor_excluded a [7,4,0,8,1,3,2,6,5] 0 5 3 8 (by decide) (by decide +kernel)

theorem node_2055 : Excluded a [7,4,0,8,1,3,2,6] :=
  branch_excluded a [7,4,0,8,1,3,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,1,3,2,6,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,6,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,6,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,6,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,6,4] (by decide +kernel))
      node_2056
      (invalid_excluded a [7,4,0,8,1,3,2,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,6,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,6,8] (by decide +kernel)))

theorem node_2052 : Excluded a [7,4,0,8,1,3,2] :=
  branch_excluded a [7,4,0,8,1,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,1,3,2,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,4] (by decide +kernel))
      node_2053
      node_2055
      (invalid_excluded a [7,4,0,8,1,3,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,2,8] (by decide +kernel)))

theorem node_2058 : Excluded a [7,4,0,8,1,3,5,2] :=
  predecessor_excluded a [7,4,0,8,1,3,5,2] 1 0 7 2 (by decide) (by decide +kernel)

theorem node_2059 : Excluded a [7,4,0,8,1,3,5,6] :=
  predecessor_excluded a [7,4,0,8,1,3,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_2057 : Excluded a [7,4,0,8,1,3,5] :=
  branch_excluded a [7,4,0,8,1,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,1,3,5,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,5,1] (by decide +kernel))
      node_2058
      (invalid_excluded a [7,4,0,8,1,3,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,5,5] (by decide +kernel))
      node_2059
      (invalid_excluded a [7,4,0,8,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,5,8] (by decide +kernel)))

theorem node_2051 : Excluded a [7,4,0,8,1,3] :=
  branch_excluded a [7,4,0,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,1] (by decide +kernel))
      node_2052
      (invalid_excluded a [7,4,0,8,1,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,4] (by decide +kernel))
      node_2057
      (invalid_excluded a [7,4,0,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,3,8] (by decide +kernel)))

theorem node_2049 : Excluded a [7,4,0,8,1] :=
  branch_excluded a [7,4,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,1] (by decide +kernel))
      node_2050
      node_2051
      (invalid_excluded a [7,4,0,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,1,8] (by decide +kernel)))

theorem node_2060 : Excluded a [7,4,0,8,2] :=
  source_excluded a [7,4,0,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2061 : Excluded a [7,4,0,8,3] :=
  predecessor_excluded a [7,4,0,8,3] 0 3 1 4 (by decide) (by decide +kernel)

theorem node_2062 : Excluded a [7,4,0,8,6] :=
  source_excluded a [7,4,0,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2048 : Excluded a [7,4,0,8] :=
  branch_excluded a [7,4,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,0] (by decide +kernel))
      node_2049
      node_2060
      node_2061
      (invalid_excluded a [7,4,0,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,5] (by decide +kernel))
      node_2062
      (invalid_excluded a [7,4,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,8] (by decide +kernel)))

theorem node_2018 : Excluded a [7,4,0] :=
  branch_excluded a [7,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,0] (by decide +kernel))
      node_2019
      node_2020
      (invalid_excluded a [7,4,0,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,4] (by decide +kernel))
      node_2021
      node_2022
      (invalid_excluded a [7,4,0,7] (by decide +kernel))
      node_2048)

theorem node_2063 : Excluded a [7,4,1] :=
  predecessor_excluded a [7,4,1] 0 4 2 1 (by decide) (by decide +kernel)

theorem node_2064 : Excluded a [7,4,5] :=
  predecessor_excluded a [7,4,5] 0 5 1 2 (by decide) (by decide +kernel)

theorem node_2067 : Excluded a [7,4,6,0,1] :=
  predecessor_excluded a [7,4,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2068 : Excluded a [7,4,6,0,2] :=
  source_excluded a [7,4,6,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2069 : Excluded a [7,4,6,0,3] :=
  predecessor_excluded a [7,4,6,0,3] 0 3 1 4 (by decide) (by decide +kernel)

theorem node_2072 : Excluded a [7,4,6,0,8,1,2] :=
  predecessor_excluded a [7,4,6,0,8,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2073 : Excluded a [7,4,6,0,8,1,3] :=
  source_excluded a [7,4,6,0,8,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2075 : Excluded a [7,4,6,0,8,1,5,2] :=
  predecessor_excluded a [7,4,6,0,8,1,5,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_2076 : Excluded a [7,4,6,0,8,1,5,3] :=
  predecessor_excluded a [7,4,6,0,8,1,5,3] 1 0 7 3 (by decide) (by decide +kernel)

theorem node_2074 : Excluded a [7,4,6,0,8,1,5] :=
  branch_excluded a [7,4,6,0,8,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,6,0,8,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,8,1,5,1] (by decide +kernel))
      node_2075
      node_2076
      (invalid_excluded a [7,4,6,0,8,1,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,8,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,8,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,8,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,8,1,5,8] (by decide +kernel)))

theorem node_2071 : Excluded a [7,4,6,0,8,1] :=
  branch_excluded a [7,4,6,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,6,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,8,1,1] (by decide +kernel))
      node_2072
      node_2073
      (invalid_excluded a [7,4,6,0,8,1,4] (by decide +kernel))
      node_2074
      (invalid_excluded a [7,4,6,0,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,8,1,8] (by decide +kernel)))

theorem node_2077 : Excluded a [7,4,6,0,8,2] :=
  source_excluded a [7,4,6,0,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2078 : Excluded a [7,4,6,0,8,3] :=
  source_excluded a [7,4,6,0,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2070 : Excluded a [7,4,6,0,8] :=
  branch_excluded a [7,4,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,6,0,8,0] (by decide +kernel))
      node_2071
      node_2077
      node_2078
      (invalid_excluded a [7,4,6,0,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,8,8] (by decide +kernel)))

theorem node_2066 : Excluded a [7,4,6,0] :=
  branch_excluded a [7,4,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,6,0,0] (by decide +kernel))
      node_2067
      node_2068
      node_2069
      (invalid_excluded a [7,4,6,0,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,0,7] (by decide +kernel))
      node_2070)

theorem node_2079 : Excluded a [7,4,6,1] :=
  source_excluded a [7,4,6,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2080 : Excluded a [7,4,6,2] :=
  source_excluded a [7,4,6,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_2081 : Excluded a [7,4,6,5] :=
  source_excluded a [7,4,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2083 : Excluded a [7,4,6,8,0] :=
  predecessor_excluded a [7,4,6,8,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_2085 : Excluded a [7,4,6,8,1,0] :=
  predecessor_excluded a [7,4,6,8,1,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2086 : Excluded a [7,4,6,8,1,2] :=
  source_excluded a [7,4,6,8,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2087 : Excluded a [7,4,6,8,1,3] :=
  source_excluded a [7,4,6,8,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2084 : Excluded a [7,4,6,8,1] :=
  branch_excluded a [7,4,6,8,1] (by decide)
    (fin9_cases _
      node_2085
      (invalid_excluded a [7,4,6,8,1,1] (by decide +kernel))
      node_2086
      node_2087
      (invalid_excluded a [7,4,6,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,1,8] (by decide +kernel)))

theorem node_2088 : Excluded a [7,4,6,8,2] :=
  source_excluded a [7,4,6,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2089 : Excluded a [7,4,6,8,3] :=
  predecessor_excluded a [7,4,6,8,3] 0 3 1 4 (by decide) (by decide +kernel)

theorem node_2082 : Excluded a [7,4,6,8] :=
  branch_excluded a [7,4,6,8] (by decide)
    (fin9_cases _
      node_2083
      node_2084
      node_2088
      node_2089
      (invalid_excluded a [7,4,6,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,8] (by decide +kernel)))

theorem node_2065 : Excluded a [7,4,6] :=
  branch_excluded a [7,4,6] (by decide)
    (fin9_cases _
      node_2066
      node_2079
      node_2080
      (invalid_excluded a [7,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,4,6,4] (by decide +kernel))
      node_2081
      (invalid_excluded a [7,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,7] (by decide +kernel))
      node_2082)

theorem node_2091 : Excluded a [7,4,8,0] :=
  predecessor_excluded a [7,4,8,0] 1 0 2 3 (by decide) (by decide +kernel)

theorem node_2092 : Excluded a [7,4,8,1] :=
  source_excluded a [7,4,8,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2093 : Excluded a [7,4,8,2] :=
  source_excluded a [7,4,8,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_2094 : Excluded a [7,4,8,5] :=
  source_excluded a [7,4,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2097 : Excluded a [7,4,8,6,0,1] :=
  predecessor_excluded a [7,4,8,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2099 : Excluded a [7,4,8,6,0,2,1] :=
  source_excluded a [7,4,8,6,0,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2100 : Excluded a [7,4,8,6,0,2,3] :=
  predecessor_excluded a [7,4,8,6,0,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_2101 : Excluded a [7,4,8,6,0,2,5] :=
  predecessor_excluded a [7,4,8,6,0,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2098 : Excluded a [7,4,8,6,0,2] :=
  branch_excluded a [7,4,8,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,8,6,0,2,0] (by decide +kernel))
      node_2099
      (invalid_excluded a [7,4,8,6,0,2,2] (by decide +kernel))
      node_2100
      (invalid_excluded a [7,4,8,6,0,2,4] (by decide +kernel))
      node_2101
      (invalid_excluded a [7,4,8,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,0,2,8] (by decide +kernel)))

theorem node_2102 : Excluded a [7,4,8,6,0,3] :=
  source_excluded a [7,4,8,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2096 : Excluded a [7,4,8,6,0] :=
  branch_excluded a [7,4,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,8,6,0,0] (by decide +kernel))
      node_2097
      node_2098
      node_2102
      (invalid_excluded a [7,4,8,6,0,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,0,8] (by decide +kernel)))

theorem node_2104 : Excluded a [7,4,8,6,1,0] :=
  predecessor_excluded a [7,4,8,6,1,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2105 : Excluded a [7,4,8,6,1,2] :=
  predecessor_excluded a [7,4,8,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2106 : Excluded a [7,4,8,6,1,3] :=
  source_excluded a [7,4,8,6,1,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2103 : Excluded a [7,4,8,6,1] :=
  branch_excluded a [7,4,8,6,1] (by decide)
    (fin9_cases _
      node_2104
      (invalid_excluded a [7,4,8,6,1,1] (by decide +kernel))
      node_2105
      node_2106
      (invalid_excluded a [7,4,8,6,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,1,8] (by decide +kernel)))

theorem node_2107 : Excluded a [7,4,8,6,2] :=
  source_excluded a [7,4,8,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2108 : Excluded a [7,4,8,6,3] :=
  predecessor_excluded a [7,4,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2095 : Excluded a [7,4,8,6] :=
  branch_excluded a [7,4,8,6] (by decide)
    (fin9_cases _
      node_2096
      node_2103
      node_2107
      node_2108
      (invalid_excluded a [7,4,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,8] (by decide +kernel)))

theorem node_2090 : Excluded a [7,4,8] :=
  branch_excluded a [7,4,8] (by decide)
    (fin9_cases _
      node_2091
      node_2092
      node_2093
      (invalid_excluded a [7,4,8,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,4] (by decide +kernel))
      node_2094
      node_2095
      (invalid_excluded a [7,4,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,8] (by decide +kernel)))

theorem node_2017 : Excluded a [7,4] :=
  branch_excluded a [7,4] (by decide)
    (fin9_cases _
      node_2018
      node_2063
      (invalid_excluded a [7,4,2] (by decide +kernel))
      (invalid_excluded a [7,4,3] (by decide +kernel))
      (invalid_excluded a [7,4,4] (by decide +kernel))
      node_2064
      node_2065
      (invalid_excluded a [7,4,7] (by decide +kernel))
      node_2090)

theorem node_2111 : Excluded a [7,5,0,1] :=
  predecessor_excluded a [7,5,0,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_2113 : Excluded a [7,5,0,2,1] :=
  source_excluded a [7,5,0,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2114 : Excluded a [7,5,0,2,3] :=
  predecessor_excluded a [7,5,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2115 : Excluded a [7,5,0,2,6] :=
  source_excluded a [7,5,0,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2119 : Excluded a [7,5,0,2,8,1,3,4] :=
  source_excluded a [7,5,0,2,8,1,3,4] 7 0 4 (by decide) (by decide +kernel)

def b_2121 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 5
  | 2 => 0
  | 3 => 2
  | 4 => 8
  | 5 => 1
  | 6 => 3
  | 7 => 6
  | 8 => 4
  | _ => 0

def cert_2121 : LosingRegion (edgeOf a b_2121) 1 :=
  losingMask a b_2121 1 1212623672352504628117505
    (by decide +kernel) (by decide +kernel)

theorem node_2121 : Excluded a [7,5,0,2,8,1,3,6,4] :=
  losing_excluded a [7,5,0,2,8,1,3,6,4] (by decide) b_2121 (by decide +kernel) 2 1 8 cert_2121 (by change 2 ≠ 1 ∧ ¬ edgeOf a b_2121 2 1 ∧ 8 ≠ 2 ∧ maskRegion 1212623672352504628117505 2 8; decide +kernel)

theorem node_2120 : Excluded a [7,5,0,2,8,1,3,6] :=
  branch_excluded a [7,5,0,2,8,1,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,2,8,1,3,6,0] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,3,6,1] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,3,6,2] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,3,6,3] (by decide +kernel))
      node_2121
      (invalid_excluded a [7,5,0,2,8,1,3,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,3,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,3,6,8] (by decide +kernel)))

theorem node_2118 : Excluded a [7,5,0,2,8,1,3] :=
  branch_excluded a [7,5,0,2,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,2,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,3,1] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,3,2] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,3,3] (by decide +kernel))
      node_2119
      (invalid_excluded a [7,5,0,2,8,1,3,5] (by decide +kernel))
      node_2120
      (invalid_excluded a [7,5,0,2,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,3,8] (by decide +kernel)))

theorem node_2122 : Excluded a [7,5,0,2,8,1,4] :=
  predecessor_excluded a [7,5,0,2,8,1,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_2117 : Excluded a [7,5,0,2,8,1] :=
  branch_excluded a [7,5,0,2,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,2,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,2] (by decide +kernel))
      node_2118
      node_2122
      (invalid_excluded a [7,5,0,2,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,1,8] (by decide +kernel)))

theorem node_2123 : Excluded a [7,5,0,2,8,3] :=
  predecessor_excluded a [7,5,0,2,8,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_2125 : Excluded a [7,5,0,2,8,4,1] :=
  source_excluded a [7,5,0,2,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2127 : Excluded a [7,5,0,2,8,4,3,1] :=
  source_excluded a [7,5,0,2,8,4,3,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2129 : Excluded a [7,5,0,2,8,4,3,6,1] :=
  source_excluded a [7,5,0,2,8,4,3,6,1] 8 2 0 (by decide) (by decide +kernel)

theorem node_2128 : Excluded a [7,5,0,2,8,4,3,6] :=
  branch_excluded a [7,5,0,2,8,4,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,2,8,4,3,6,0] (by decide +kernel))
      node_2129
      (invalid_excluded a [7,5,0,2,8,4,3,6,2] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,6,8] (by decide +kernel)))

theorem node_2126 : Excluded a [7,5,0,2,8,4,3] :=
  branch_excluded a [7,5,0,2,8,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,2,8,4,3,0] (by decide +kernel))
      node_2127
      (invalid_excluded a [7,5,0,2,8,4,3,2] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,5] (by decide +kernel))
      node_2128
      (invalid_excluded a [7,5,0,2,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,8] (by decide +kernel)))

theorem node_2124 : Excluded a [7,5,0,2,8,4] :=
  branch_excluded a [7,5,0,2,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,2,8,4,0] (by decide +kernel))
      node_2125
      (invalid_excluded a [7,5,0,2,8,4,2] (by decide +kernel))
      node_2126
      (invalid_excluded a [7,5,0,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,8] (by decide +kernel)))

theorem node_2116 : Excluded a [7,5,0,2,8] :=
  branch_excluded a [7,5,0,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,2,8,0] (by decide +kernel))
      node_2117
      (invalid_excluded a [7,5,0,2,8,2] (by decide +kernel))
      node_2123
      node_2124
      (invalid_excluded a [7,5,0,2,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,8] (by decide +kernel)))

theorem node_2112 : Excluded a [7,5,0,2] :=
  branch_excluded a [7,5,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,2,0] (by decide +kernel))
      node_2113
      (invalid_excluded a [7,5,0,2,2] (by decide +kernel))
      node_2114
      (invalid_excluded a [7,5,0,2,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,5] (by decide +kernel))
      node_2115
      (invalid_excluded a [7,5,0,2,7] (by decide +kernel))
      node_2116)

theorem node_2131 : Excluded a [7,5,0,6,1] :=
  source_excluded a [7,5,0,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2132 : Excluded a [7,5,0,6,2] :=
  source_excluded a [7,5,0,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2133 : Excluded a [7,5,0,6,3] :=
  predecessor_excluded a [7,5,0,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2136 : Excluded a [7,5,0,6,8,1,2] :=
  predecessor_excluded a [7,5,0,6,8,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2138 : Excluded a [7,5,0,6,8,1,3,2] :=
  predecessor_excluded a [7,5,0,6,8,1,3,2] 1 0 7 2 (by decide) (by decide +kernel)

theorem node_2139 : Excluded a [7,5,0,6,8,1,3,4] :=
  source_excluded a [7,5,0,6,8,1,3,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_2137 : Excluded a [7,5,0,6,8,1,3] :=
  branch_excluded a [7,5,0,6,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,6,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,1,3,1] (by decide +kernel))
      node_2138
      (invalid_excluded a [7,5,0,6,8,1,3,3] (by decide +kernel))
      node_2139
      (invalid_excluded a [7,5,0,6,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,1,3,8] (by decide +kernel)))

theorem node_2140 : Excluded a [7,5,0,6,8,1,4] :=
  source_excluded a [7,5,0,6,8,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2135 : Excluded a [7,5,0,6,8,1] :=
  branch_excluded a [7,5,0,6,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,6,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,1,1] (by decide +kernel))
      node_2136
      node_2137
      node_2140
      (invalid_excluded a [7,5,0,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,1,8] (by decide +kernel)))

theorem node_2141 : Excluded a [7,5,0,6,8,2] :=
  source_excluded a [7,5,0,6,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2142 : Excluded a [7,5,0,6,8,3] :=
  source_excluded a [7,5,0,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2143 : Excluded a [7,5,0,6,8,4] :=
  source_excluded a [7,5,0,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2134 : Excluded a [7,5,0,6,8] :=
  branch_excluded a [7,5,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,6,8,0] (by decide +kernel))
      node_2135
      node_2141
      node_2142
      node_2143
      (invalid_excluded a [7,5,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,8] (by decide +kernel)))

theorem node_2130 : Excluded a [7,5,0,6] :=
  branch_excluded a [7,5,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,6,0] (by decide +kernel))
      node_2131
      node_2132
      node_2133
      (invalid_excluded a [7,5,0,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,7] (by decide +kernel))
      node_2134)

theorem node_2145 : Excluded a [7,5,0,8,1] :=
  source_excluded a [7,5,0,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2146 : Excluded a [7,5,0,8,2] :=
  source_excluded a [7,5,0,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2149 : Excluded a [7,5,0,8,3,1,2] :=
  predecessor_excluded a [7,5,0,8,3,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2151 : Excluded a [7,5,0,8,3,1,4,2] :=
  predecessor_excluded a [7,5,0,8,3,1,4,2] 1 0 7 2 (by decide) (by decide +kernel)

theorem node_2153 : Excluded a [7,5,0,8,3,1,4,6,2] :=
  source_excluded a [7,5,0,8,3,1,4,6,2] 8 1 2 (by decide) (by decide +kernel)

theorem node_2152 : Excluded a [7,5,0,8,3,1,4,6] :=
  branch_excluded a [7,5,0,8,3,1,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,8,3,1,4,6,0] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,1,4,6,1] (by decide +kernel))
      node_2153
      (invalid_excluded a [7,5,0,8,3,1,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,1,4,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,1,4,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,1,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,1,4,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,1,4,6,8] (by decide +kernel)))

theorem node_2150 : Excluded a [7,5,0,8,3,1,4] :=
  branch_excluded a [7,5,0,8,3,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,8,3,1,4,0] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,1,4,1] (by decide +kernel))
      node_2151
      (invalid_excluded a [7,5,0,8,3,1,4,3] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,1,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,1,4,5] (by decide +kernel))
      node_2152
      (invalid_excluded a [7,5,0,8,3,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,1,4,8] (by decide +kernel)))

theorem node_2148 : Excluded a [7,5,0,8,3,1] :=
  branch_excluded a [7,5,0,8,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,8,3,1,0] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,1,1] (by decide +kernel))
      node_2149
      (invalid_excluded a [7,5,0,8,3,1,3] (by decide +kernel))
      node_2150
      (invalid_excluded a [7,5,0,8,3,1,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,1,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,1,8] (by decide +kernel)))

theorem node_2154 : Excluded a [7,5,0,8,3,2] :=
  source_excluded a [7,5,0,8,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2155 : Excluded a [7,5,0,8,3,4] :=
  predecessor_excluded a [7,5,0,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2147 : Excluded a [7,5,0,8,3] :=
  branch_excluded a [7,5,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,8,3,0] (by decide +kernel))
      node_2148
      node_2154
      (invalid_excluded a [7,5,0,8,3,3] (by decide +kernel))
      node_2155
      (invalid_excluded a [7,5,0,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,8] (by decide +kernel)))

theorem node_2156 : Excluded a [7,5,0,8,6] :=
  source_excluded a [7,5,0,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2144 : Excluded a [7,5,0,8] :=
  branch_excluded a [7,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,8,0] (by decide +kernel))
      node_2145
      node_2146
      node_2147
      (invalid_excluded a [7,5,0,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,5] (by decide +kernel))
      node_2156
      (invalid_excluded a [7,5,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,8] (by decide +kernel)))

theorem node_2110 : Excluded a [7,5,0] :=
  branch_excluded a [7,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,0] (by decide +kernel))
      node_2111
      node_2112
      (invalid_excluded a [7,5,0,3] (by decide +kernel))
      (invalid_excluded a [7,5,0,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,5] (by decide +kernel))
      node_2130
      (invalid_excluded a [7,5,0,7] (by decide +kernel))
      node_2144)

theorem node_2159 : Excluded a [7,5,1,0,2] :=
  source_excluded a [7,5,1,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2161 : Excluded a [7,5,1,0,3,2] :=
  source_excluded a [7,5,1,0,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2162 : Excluded a [7,5,1,0,3,4] :=
  predecessor_excluded a [7,5,1,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2166 : Excluded a [7,5,1,0,3,8,2,4,6] :=
  source_excluded a [7,5,1,0,3,8,2,4,6] 5 0 8 (by decide) (by decide +kernel)

theorem node_2165 : Excluded a [7,5,1,0,3,8,2,4] :=
  branch_excluded a [7,5,1,0,3,8,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,0,3,8,2,4,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,2,4,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,2,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,2,4,5] (by decide +kernel))
      node_2166
      (invalid_excluded a [7,5,1,0,3,8,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,2,4,8] (by decide +kernel)))

theorem node_2167 : Excluded a [7,5,1,0,3,8,2,6] :=
  source_excluded a [7,5,1,0,3,8,2,6] 5 0 7 (by decide) (by decide +kernel)

theorem node_2164 : Excluded a [7,5,1,0,3,8,2] :=
  branch_excluded a [7,5,1,0,3,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,0,3,8,2,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,2,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,2,2] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,2,3] (by decide +kernel))
      node_2165
      (invalid_excluded a [7,5,1,0,3,8,2,5] (by decide +kernel))
      node_2167
      (invalid_excluded a [7,5,1,0,3,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,2,8] (by decide +kernel)))

theorem node_2169 : Excluded a [7,5,1,0,3,8,4,2] :=
  predecessor_excluded a [7,5,1,0,3,8,4,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_2170 : Excluded a [7,5,1,0,3,8,4,6] :=
  source_excluded a [7,5,1,0,3,8,4,6] 5 0 7 (by decide) (by decide +kernel)

theorem node_2168 : Excluded a [7,5,1,0,3,8,4] :=
  branch_excluded a [7,5,1,0,3,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,0,3,8,4,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,4,1] (by decide +kernel))
      node_2169
      (invalid_excluded a [7,5,1,0,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,4,5] (by decide +kernel))
      node_2170
      (invalid_excluded a [7,5,1,0,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,4,8] (by decide +kernel)))

theorem node_2163 : Excluded a [7,5,1,0,3,8] :=
  branch_excluded a [7,5,1,0,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,0,3,8,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,1] (by decide +kernel))
      node_2164
      (invalid_excluded a [7,5,1,0,3,8,3] (by decide +kernel))
      node_2168
      (invalid_excluded a [7,5,1,0,3,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,8,8] (by decide +kernel)))

theorem node_2160 : Excluded a [7,5,1,0,3] :=
  branch_excluded a [7,5,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,1] (by decide +kernel))
      node_2161
      (invalid_excluded a [7,5,1,0,3,3] (by decide +kernel))
      node_2162
      (invalid_excluded a [7,5,1,0,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,3,7] (by decide +kernel))
      node_2163)

theorem node_2171 : Excluded a [7,5,1,0,6] :=
  source_excluded a [7,5,1,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2173 : Excluded a [7,5,1,0,8,2] :=
  source_excluded a [7,5,1,0,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2174 : Excluded a [7,5,1,0,8,3] :=
  predecessor_excluded a [7,5,1,0,8,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_2177 : Excluded a [7,5,1,0,8,4,2,3] :=
  predecessor_excluded a [7,5,1,0,8,4,2,3] 1 0 7 3 (by decide) (by decide +kernel)

theorem node_2179 : Excluded a [7,5,1,0,8,4,2,6,3] :=
  source_excluded a [7,5,1,0,8,4,2,6,3] 8 1 3 (by decide) (by decide +kernel)

theorem node_2178 : Excluded a [7,5,1,0,8,4,2,6] :=
  branch_excluded a [7,5,1,0,8,4,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,0,8,4,2,6,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,2,6,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,2,6,2] (by decide +kernel))
      node_2179
      (invalid_excluded a [7,5,1,0,8,4,2,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,2,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,2,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,2,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,2,6,8] (by decide +kernel)))

theorem node_2176 : Excluded a [7,5,1,0,8,4,2] :=
  branch_excluded a [7,5,1,0,8,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,0,8,4,2,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,2,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,2,2] (by decide +kernel))
      node_2177
      (invalid_excluded a [7,5,1,0,8,4,2,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,2,5] (by decide +kernel))
      node_2178
      (invalid_excluded a [7,5,1,0,8,4,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,2,8] (by decide +kernel)))

theorem node_2181 : Excluded a [7,5,1,0,8,4,3,2] :=
  predecessor_excluded a [7,5,1,0,8,4,3,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_2183 : Excluded a [7,5,1,0,8,4,3,6,2] :=
  predecessor_excluded a [7,5,1,0,8,4,3,6,2] 3 1 8 2 (by decide) (by decide +kernel)

theorem node_2182 : Excluded a [7,5,1,0,8,4,3,6] :=
  branch_excluded a [7,5,1,0,8,4,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,0,8,4,3,6,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,3,6,1] (by decide +kernel))
      node_2183
      (invalid_excluded a [7,5,1,0,8,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,3,6,8] (by decide +kernel)))

theorem node_2180 : Excluded a [7,5,1,0,8,4,3] :=
  branch_excluded a [7,5,1,0,8,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,0,8,4,3,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,3,1] (by decide +kernel))
      node_2181
      (invalid_excluded a [7,5,1,0,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,3,5] (by decide +kernel))
      node_2182
      (invalid_excluded a [7,5,1,0,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,3,8] (by decide +kernel)))

theorem node_2175 : Excluded a [7,5,1,0,8,4] :=
  branch_excluded a [7,5,1,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,0,8,4,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,1] (by decide +kernel))
      node_2176
      node_2180
      (invalid_excluded a [7,5,1,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,4,8] (by decide +kernel)))

theorem node_2172 : Excluded a [7,5,1,0,8] :=
  branch_excluded a [7,5,1,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,0,8,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,1] (by decide +kernel))
      node_2173
      node_2174
      node_2175
      (invalid_excluded a [7,5,1,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,8,8] (by decide +kernel)))

theorem node_2158 : Excluded a [7,5,1,0] :=
  branch_excluded a [7,5,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,0,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,1] (by decide +kernel))
      node_2159
      node_2160
      (invalid_excluded a [7,5,1,0,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,0,5] (by decide +kernel))
      node_2171
      (invalid_excluded a [7,5,1,0,7] (by decide +kernel))
      node_2172)

theorem node_2184 : Excluded a [7,5,1,2] :=
  predecessor_excluded a [7,5,1,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_2187 : Excluded a [7,5,1,6,0,2] :=
  source_excluded a [7,5,1,6,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2188 : Excluded a [7,5,1,6,0,3] :=
  source_excluded a [7,5,1,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2189 : Excluded a [7,5,1,6,0,4] :=
  source_excluded a [7,5,1,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2192 : Excluded a [7,5,1,6,0,8,2,3] :=
  predecessor_excluded a [7,5,1,6,0,8,2,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_2193 : Excluded a [7,5,1,6,0,8,2,4] :=
  predecessor_excluded a [7,5,1,6,0,8,2,4] 1 0 7 4 (by decide) (by decide +kernel)

theorem node_2191 : Excluded a [7,5,1,6,0,8,2] :=
  branch_excluded a [7,5,1,6,0,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,6,0,8,2,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,8,2,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,8,2,2] (by decide +kernel))
      node_2192
      node_2193
      (invalid_excluded a [7,5,1,6,0,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,8,2,8] (by decide +kernel)))

theorem node_2195 : Excluded a [7,5,1,6,0,8,3,2] :=
  predecessor_excluded a [7,5,1,6,0,8,3,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_2196 : Excluded a [7,5,1,6,0,8,3,4] :=
  predecessor_excluded a [7,5,1,6,0,8,3,4] 1 0 7 4 (by decide) (by decide +kernel)

theorem node_2194 : Excluded a [7,5,1,6,0,8,3] :=
  branch_excluded a [7,5,1,6,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,6,0,8,3,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,8,3,1] (by decide +kernel))
      node_2195
      (invalid_excluded a [7,5,1,6,0,8,3,3] (by decide +kernel))
      node_2196
      (invalid_excluded a [7,5,1,6,0,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,8,3,8] (by decide +kernel)))

theorem node_2197 : Excluded a [7,5,1,6,0,8,4] :=
  source_excluded a [7,5,1,6,0,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2190 : Excluded a [7,5,1,6,0,8] :=
  branch_excluded a [7,5,1,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,6,0,8,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,8,1] (by decide +kernel))
      node_2191
      node_2194
      node_2197
      (invalid_excluded a [7,5,1,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,8,8] (by decide +kernel)))

theorem node_2186 : Excluded a [7,5,1,6,0] :=
  branch_excluded a [7,5,1,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,1,6,0,0] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,1] (by decide +kernel))
      node_2187
      node_2188
      node_2189
      (invalid_excluded a [7,5,1,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,0,7] (by decide +kernel))
      node_2190)

theorem node_2198 : Excluded a [7,5,1,6,2] :=
  source_excluded a [7,5,1,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2199 : Excluded a [7,5,1,6,3] :=
  predecessor_excluded a [7,5,1,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2201 : Excluded a [7,5,1,6,8,0] :=
  predecessor_excluded a [7,5,1,6,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2202 : Excluded a [7,5,1,6,8,2] :=
  source_excluded a [7,5,1,6,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2203 : Excluded a [7,5,1,6,8,3] :=
  source_excluded a [7,5,1,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2204 : Excluded a [7,5,1,6,8,4] :=
  source_excluded a [7,5,1,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2200 : Excluded a [7,5,1,6,8] :=
  branch_excluded a [7,5,1,6,8] (by decide)
    (fin9_cases _
      node_2201
      (invalid_excluded a [7,5,1,6,8,1] (by decide +kernel))
      node_2202
      node_2203
      node_2204
      (invalid_excluded a [7,5,1,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,8,8] (by decide +kernel)))

theorem node_2185 : Excluded a [7,5,1,6] :=
  branch_excluded a [7,5,1,6] (by decide)
    (fin9_cases _
      node_2186
      (invalid_excluded a [7,5,1,6,1] (by decide +kernel))
      node_2198
      node_2199
      (invalid_excluded a [7,5,1,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,7] (by decide +kernel))
      node_2200)

theorem node_2206 : Excluded a [7,5,1,8,0] :=
  predecessor_excluded a [7,5,1,8,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_2207 : Excluded a [7,5,1,8,2] :=
  source_excluded a [7,5,1,8,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2209 : Excluded a [7,5,1,8,3,0] :=
  predecessor_excluded a [7,5,1,8,3,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2210 : Excluded a [7,5,1,8,3,2] :=
  source_excluded a [7,5,1,8,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2211 : Excluded a [7,5,1,8,3,4] :=
  predecessor_excluded a [7,5,1,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2208 : Excluded a [7,5,1,8,3] :=
  branch_excluded a [7,5,1,8,3] (by decide)
    (fin9_cases _
      node_2209
      (invalid_excluded a [7,5,1,8,3,1] (by decide +kernel))
      node_2210
      (invalid_excluded a [7,5,1,8,3,3] (by decide +kernel))
      node_2211
      (invalid_excluded a [7,5,1,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,8] (by decide +kernel)))

theorem node_2212 : Excluded a [7,5,1,8,6] :=
  source_excluded a [7,5,1,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2205 : Excluded a [7,5,1,8] :=
  branch_excluded a [7,5,1,8] (by decide)
    (fin9_cases _
      node_2206
      (invalid_excluded a [7,5,1,8,1] (by decide +kernel))
      node_2207
      node_2208
      (invalid_excluded a [7,5,1,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,5] (by decide +kernel))
      node_2212
      (invalid_excluded a [7,5,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,8] (by decide +kernel)))

theorem node_2157 : Excluded a [7,5,1] :=
  branch_excluded a [7,5,1] (by decide)
    (fin9_cases _
      node_2158
      (invalid_excluded a [7,5,1,1] (by decide +kernel))
      node_2184
      (invalid_excluded a [7,5,1,3] (by decide +kernel))
      (invalid_excluded a [7,5,1,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,5] (by decide +kernel))
      node_2185
      (invalid_excluded a [7,5,1,7] (by decide +kernel))
      node_2205)

theorem node_2213 : Excluded a [7,5,4] :=
  source_excluded a [7,5,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2214 : Excluded a [7,5,6] :=
  predecessor_excluded a [7,5,6] 0 6 1 2 (by decide) (by decide +kernel)

theorem node_2216 : Excluded a [7,5,8,0] :=
  predecessor_excluded a [7,5,8,0] 1 0 2 3 (by decide) (by decide +kernel)

theorem node_2217 : Excluded a [7,5,8,1] :=
  predecessor_excluded a [7,5,8,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_2220 : Excluded a [7,5,8,2,0,1] :=
  predecessor_excluded a [7,5,8,2,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2221 : Excluded a [7,5,8,2,0,3] :=
  predecessor_excluded a [7,5,8,2,0,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_2223 : Excluded a [7,5,8,2,0,4,1] :=
  source_excluded a [7,5,8,2,0,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2225 : Excluded a [7,5,8,2,0,4,3,1] :=
  source_excluded a [7,5,8,2,0,4,3,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2227 : Excluded a [7,5,8,2,0,4,3,6,1] :=
  source_excluded a [7,5,8,2,0,4,3,6,1] 8 2 0 (by decide) (by decide +kernel)

theorem node_2226 : Excluded a [7,5,8,2,0,4,3,6] :=
  branch_excluded a [7,5,8,2,0,4,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,2,0,4,3,6,0] (by decide +kernel))
      node_2227
      (invalid_excluded a [7,5,8,2,0,4,3,6,2] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,4,3,6,8] (by decide +kernel)))

theorem node_2224 : Excluded a [7,5,8,2,0,4,3] :=
  branch_excluded a [7,5,8,2,0,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,2,0,4,3,0] (by decide +kernel))
      node_2225
      (invalid_excluded a [7,5,8,2,0,4,3,2] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,4,3,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,4,3,5] (by decide +kernel))
      node_2226
      (invalid_excluded a [7,5,8,2,0,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,4,3,8] (by decide +kernel)))

theorem node_2222 : Excluded a [7,5,8,2,0,4] :=
  branch_excluded a [7,5,8,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,2,0,4,0] (by decide +kernel))
      node_2223
      (invalid_excluded a [7,5,8,2,0,4,2] (by decide +kernel))
      node_2224
      (invalid_excluded a [7,5,8,2,0,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,4,8] (by decide +kernel)))

theorem node_2219 : Excluded a [7,5,8,2,0] :=
  branch_excluded a [7,5,8,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,2,0,0] (by decide +kernel))
      node_2220
      (invalid_excluded a [7,5,8,2,0,2] (by decide +kernel))
      node_2221
      node_2222
      (invalid_excluded a [7,5,8,2,0,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,0,8] (by decide +kernel)))

theorem node_2228 : Excluded a [7,5,8,2,1] :=
  source_excluded a [7,5,8,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2229 : Excluded a [7,5,8,2,3] :=
  predecessor_excluded a [7,5,8,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2230 : Excluded a [7,5,8,2,6] :=
  source_excluded a [7,5,8,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2218 : Excluded a [7,5,8,2] :=
  branch_excluded a [7,5,8,2] (by decide)
    (fin9_cases _
      node_2219
      node_2228
      (invalid_excluded a [7,5,8,2,2] (by decide +kernel))
      node_2229
      (invalid_excluded a [7,5,8,2,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,5] (by decide +kernel))
      node_2230
      (invalid_excluded a [7,5,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,2,8] (by decide +kernel)))

theorem node_2233 : Excluded a [7,5,8,6,0,1] :=
  predecessor_excluded a [7,5,8,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2234 : Excluded a [7,5,8,6,0,2] :=
  source_excluded a [7,5,8,6,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2235 : Excluded a [7,5,8,6,0,3] :=
  source_excluded a [7,5,8,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2236 : Excluded a [7,5,8,6,0,4] :=
  source_excluded a [7,5,8,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2232 : Excluded a [7,5,8,6,0] :=
  branch_excluded a [7,5,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,6,0,0] (by decide +kernel))
      node_2233
      node_2234
      node_2235
      node_2236
      (invalid_excluded a [7,5,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,8] (by decide +kernel)))

theorem node_2237 : Excluded a [7,5,8,6,1] :=
  source_excluded a [7,5,8,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2238 : Excluded a [7,5,8,6,2] :=
  source_excluded a [7,5,8,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2239 : Excluded a [7,5,8,6,3] :=
  predecessor_excluded a [7,5,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2231 : Excluded a [7,5,8,6] :=
  branch_excluded a [7,5,8,6] (by decide)
    (fin9_cases _
      node_2232
      node_2237
      node_2238
      node_2239
      (invalid_excluded a [7,5,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,8] (by decide +kernel)))

theorem node_2215 : Excluded a [7,5,8] :=
  branch_excluded a [7,5,8] (by decide)
    (fin9_cases _
      node_2216
      node_2217
      node_2218
      (invalid_excluded a [7,5,8,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,5] (by decide +kernel))
      node_2231
      (invalid_excluded a [7,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,8] (by decide +kernel)))

theorem node_2109 : Excluded a [7,5] :=
  branch_excluded a [7,5] (by decide)
    (fin9_cases _
      node_2110
      node_2157
      (invalid_excluded a [7,5,2] (by decide +kernel))
      (invalid_excluded a [7,5,3] (by decide +kernel))
      node_2213
      (invalid_excluded a [7,5,5] (by decide +kernel))
      node_2214
      (invalid_excluded a [7,5,7] (by decide +kernel))
      node_2215)

theorem node_2242 : Excluded a [7,6,0,1] :=
  predecessor_excluded a [7,6,0,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_2244 : Excluded a [7,6,0,2,1] :=
  predecessor_excluded a [7,6,0,2,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2245 : Excluded a [7,6,0,2,3] :=
  predecessor_excluded a [7,6,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2247 : Excluded a [7,6,0,2,8,1] :=
  source_excluded a [7,6,0,2,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2249 : Excluded a [7,6,0,2,8,3,1] :=
  source_excluded a [7,6,0,2,8,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2250 : Excluded a [7,6,0,2,8,3,4] :=
  predecessor_excluded a [7,6,0,2,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_2252 : Excluded a [7,6,0,2,8,3,5,1] :=
  source_excluded a [7,6,0,2,8,3,5,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2253 : Excluded a [7,6,0,2,8,3,5,4] :=
  source_excluded a [7,6,0,2,8,3,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_2251 : Excluded a [7,6,0,2,8,3,5] :=
  branch_excluded a [7,6,0,2,8,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,0,2,8,3,5,0] (by decide +kernel))
      node_2252
      (invalid_excluded a [7,6,0,2,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,8,3,5,3] (by decide +kernel))
      node_2253
      (invalid_excluded a [7,6,0,2,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,8,3,5,8] (by decide +kernel)))

theorem node_2248 : Excluded a [7,6,0,2,8,3] :=
  branch_excluded a [7,6,0,2,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,0,2,8,3,0] (by decide +kernel))
      node_2249
      (invalid_excluded a [7,6,0,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,8,3,3] (by decide +kernel))
      node_2250
      node_2251
      (invalid_excluded a [7,6,0,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,8,3,8] (by decide +kernel)))

theorem node_2255 : Excluded a [7,6,0,2,8,4,1] :=
  source_excluded a [7,6,0,2,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2256 : Excluded a [7,6,0,2,8,4,3] :=
  predecessor_excluded a [7,6,0,2,8,4,3] 0 3 1 6 (by decide) (by decide +kernel)

theorem node_2257 : Excluded a [7,6,0,2,8,4,5] :=
  predecessor_excluded a [7,6,0,2,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2254 : Excluded a [7,6,0,2,8,4] :=
  branch_excluded a [7,6,0,2,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,0,2,8,4,0] (by decide +kernel))
      node_2255
      (invalid_excluded a [7,6,0,2,8,4,2] (by decide +kernel))
      node_2256
      (invalid_excluded a [7,6,0,2,8,4,4] (by decide +kernel))
      node_2257
      (invalid_excluded a [7,6,0,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,8,4,8] (by decide +kernel)))

theorem node_2246 : Excluded a [7,6,0,2,8] :=
  branch_excluded a [7,6,0,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,0,2,8,0] (by decide +kernel))
      node_2247
      (invalid_excluded a [7,6,0,2,8,2] (by decide +kernel))
      node_2248
      node_2254
      (invalid_excluded a [7,6,0,2,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,8,8] (by decide +kernel)))

theorem node_2243 : Excluded a [7,6,0,2] :=
  branch_excluded a [7,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,0,2,0] (by decide +kernel))
      node_2244
      (invalid_excluded a [7,6,0,2,2] (by decide +kernel))
      node_2245
      (invalid_excluded a [7,6,0,2,4] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,0,2,7] (by decide +kernel))
      node_2246)

theorem node_2258 : Excluded a [7,6,0,5] :=
  source_excluded a [7,6,0,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2260 : Excluded a [7,6,0,8,1] :=
  predecessor_excluded a [7,6,0,8,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2262 : Excluded a [7,6,0,8,2,1] :=
  source_excluded a [7,6,0,8,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2263 : Excluded a [7,6,0,8,2,3] :=
  predecessor_excluded a [7,6,0,8,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_2265 : Excluded a [7,6,0,8,2,4,1] :=
  source_excluded a [7,6,0,8,2,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2266 : Excluded a [7,6,0,8,2,4,3] :=
  predecessor_excluded a [7,6,0,8,2,4,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_2267 : Excluded a [7,6,0,8,2,4,5] :=
  predecessor_excluded a [7,6,0,8,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2264 : Excluded a [7,6,0,8,2,4] :=
  branch_excluded a [7,6,0,8,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,0,8,2,4,0] (by decide +kernel))
      node_2265
      (invalid_excluded a [7,6,0,8,2,4,2] (by decide +kernel))
      node_2266
      (invalid_excluded a [7,6,0,8,2,4,4] (by decide +kernel))
      node_2267
      (invalid_excluded a [7,6,0,8,2,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,0,8,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,0,8,2,4,8] (by decide +kernel)))

theorem node_2261 : Excluded a [7,6,0,8,2] :=
  branch_excluded a [7,6,0,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,0,8,2,0] (by decide +kernel))
      node_2262
      (invalid_excluded a [7,6,0,8,2,2] (by decide +kernel))
      node_2263
      node_2264
      (invalid_excluded a [7,6,0,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,0,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,0,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,6,0,8,2,8] (by decide +kernel)))

theorem node_2269 : Excluded a [7,6,0,8,3,1] :=
  source_excluded a [7,6,0,8,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2270 : Excluded a [7,6,0,8,3,2] :=
  source_excluded a [7,6,0,8,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2271 : Excluded a [7,6,0,8,3,4] :=
  predecessor_excluded a [7,6,0,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2268 : Excluded a [7,6,0,8,3] :=
  branch_excluded a [7,6,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,0,8,3,0] (by decide +kernel))
      node_2269
      node_2270
      (invalid_excluded a [7,6,0,8,3,3] (by decide +kernel))
      node_2271
      (invalid_excluded a [7,6,0,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,6,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,0,8,3,8] (by decide +kernel)))

theorem node_2259 : Excluded a [7,6,0,8] :=
  branch_excluded a [7,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,0,8,0] (by decide +kernel))
      node_2260
      node_2261
      node_2268
      (invalid_excluded a [7,6,0,8,4] (by decide +kernel))
      (invalid_excluded a [7,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,0,8,8] (by decide +kernel)))

theorem node_2241 : Excluded a [7,6,0] :=
  branch_excluded a [7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,0,0] (by decide +kernel))
      node_2242
      node_2243
      (invalid_excluded a [7,6,0,3] (by decide +kernel))
      (invalid_excluded a [7,6,0,4] (by decide +kernel))
      node_2258
      (invalid_excluded a [7,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,0,7] (by decide +kernel))
      node_2259)

theorem node_2275 : Excluded a [7,6,1,0,2,3] :=
  predecessor_excluded a [7,6,1,0,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_2277 : Excluded a [7,6,1,0,2,4,3] :=
  predecessor_excluded a [7,6,1,0,2,4,3] 0 3 1 6 (by decide) (by decide +kernel)

theorem node_2278 : Excluded a [7,6,1,0,2,4,5] :=
  predecessor_excluded a [7,6,1,0,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2279 : Excluded a [7,6,1,0,2,4,8] :=
  source_excluded a [7,6,1,0,2,4,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_2276 : Excluded a [7,6,1,0,2,4] :=
  branch_excluded a [7,6,1,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,1,0,2,4,0] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,4,1] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,4,2] (by decide +kernel))
      node_2277
      (invalid_excluded a [7,6,1,0,2,4,4] (by decide +kernel))
      node_2278
      (invalid_excluded a [7,6,1,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,4,7] (by decide +kernel))
      node_2279)

theorem node_2281 : Excluded a [7,6,1,0,2,8,3] :=
  predecessor_excluded a [7,6,1,0,2,8,3] 0 3 1 6 (by decide) (by decide +kernel)

theorem node_2283 : Excluded a [7,6,1,0,2,8,4,3] :=
  predecessor_excluded a [7,6,1,0,2,8,4,3] 1 0 7 3 (by decide) (by decide +kernel)

theorem node_2284 : Excluded a [7,6,1,0,2,8,4,5] :=
  source_excluded a [7,6,1,0,2,8,4,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_2282 : Excluded a [7,6,1,0,2,8,4] :=
  branch_excluded a [7,6,1,0,2,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,1,0,2,8,4,0] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,8,4,1] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,8,4,2] (by decide +kernel))
      node_2283
      (invalid_excluded a [7,6,1,0,2,8,4,4] (by decide +kernel))
      node_2284
      (invalid_excluded a [7,6,1,0,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,8,4,8] (by decide +kernel)))

theorem node_2285 : Excluded a [7,6,1,0,2,8,5] :=
  predecessor_excluded a [7,6,1,0,2,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_2280 : Excluded a [7,6,1,0,2,8] :=
  branch_excluded a [7,6,1,0,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,1,0,2,8,0] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,8,1] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,8,2] (by decide +kernel))
      node_2281
      node_2282
      node_2285
      (invalid_excluded a [7,6,1,0,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,8,8] (by decide +kernel)))

theorem node_2274 : Excluded a [7,6,1,0,2] :=
  branch_excluded a [7,6,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,2] (by decide +kernel))
      node_2275
      node_2276
      (invalid_excluded a [7,6,1,0,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,2,7] (by decide +kernel))
      node_2280)

theorem node_2287 : Excluded a [7,6,1,0,3,2] :=
  source_excluded a [7,6,1,0,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2288 : Excluded a [7,6,1,0,3,4] :=
  predecessor_excluded a [7,6,1,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2290 : Excluded a [7,6,1,0,3,8,2] :=
  source_excluded a [7,6,1,0,3,8,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2292 : Excluded a [7,6,1,0,3,8,4,2] :=
  predecessor_excluded a [7,6,1,0,3,8,4,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_2293 : Excluded a [7,6,1,0,3,8,4,5] :=
  source_excluded a [7,6,1,0,3,8,4,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_2291 : Excluded a [7,6,1,0,3,8,4] :=
  branch_excluded a [7,6,1,0,3,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,1,0,3,8,4,0] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,3,8,4,1] (by decide +kernel))
      node_2292
      (invalid_excluded a [7,6,1,0,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,3,8,4,4] (by decide +kernel))
      node_2293
      (invalid_excluded a [7,6,1,0,3,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,3,8,4,8] (by decide +kernel)))

theorem node_2294 : Excluded a [7,6,1,0,3,8,5] :=
  predecessor_excluded a [7,6,1,0,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_2289 : Excluded a [7,6,1,0,3,8] :=
  branch_excluded a [7,6,1,0,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,1,0,3,8,0] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,3,8,1] (by decide +kernel))
      node_2290
      (invalid_excluded a [7,6,1,0,3,8,3] (by decide +kernel))
      node_2291
      node_2294
      (invalid_excluded a [7,6,1,0,3,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,3,8,8] (by decide +kernel)))

theorem node_2286 : Excluded a [7,6,1,0,3] :=
  branch_excluded a [7,6,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,3,1] (by decide +kernel))
      node_2287
      (invalid_excluded a [7,6,1,0,3,3] (by decide +kernel))
      node_2288
      (invalid_excluded a [7,6,1,0,3,5] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,3,7] (by decide +kernel))
      node_2289)

theorem node_2296 : Excluded a [7,6,1,0,8,2] :=
  source_excluded a [7,6,1,0,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2298 : Excluded a [7,6,1,0,8,3,2] :=
  source_excluded a [7,6,1,0,8,3,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2299 : Excluded a [7,6,1,0,8,3,4] :=
  predecessor_excluded a [7,6,1,0,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_2301 : Excluded a [7,6,1,0,8,3,5,2] :=
  predecessor_excluded a [7,6,1,0,8,3,5,2] 3 2 0 7 (by decide) (by decide +kernel)

theorem node_2302 : Excluded a [7,6,1,0,8,3,5,4] :=
  source_excluded a [7,6,1,0,8,3,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_2300 : Excluded a [7,6,1,0,8,3,5] :=
  branch_excluded a [7,6,1,0,8,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,1,0,8,3,5,0] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,8,3,5,1] (by decide +kernel))
      node_2301
      (invalid_excluded a [7,6,1,0,8,3,5,3] (by decide +kernel))
      node_2302
      (invalid_excluded a [7,6,1,0,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,8,3,5,8] (by decide +kernel)))

theorem node_2297 : Excluded a [7,6,1,0,8,3] :=
  branch_excluded a [7,6,1,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,1,0,8,3,0] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,8,3,1] (by decide +kernel))
      node_2298
      (invalid_excluded a [7,6,1,0,8,3,3] (by decide +kernel))
      node_2299
      node_2300
      (invalid_excluded a [7,6,1,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,8,3,8] (by decide +kernel)))

theorem node_2304 : Excluded a [7,6,1,0,8,4,2] :=
  source_excluded a [7,6,1,0,8,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2305 : Excluded a [7,6,1,0,8,4,3] :=
  predecessor_excluded a [7,6,1,0,8,4,3] 0 3 1 6 (by decide) (by decide +kernel)

theorem node_2306 : Excluded a [7,6,1,0,8,4,5] :=
  predecessor_excluded a [7,6,1,0,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2303 : Excluded a [7,6,1,0,8,4] :=
  branch_excluded a [7,6,1,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,1,0,8,4,0] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,8,4,1] (by decide +kernel))
      node_2304
      node_2305
      (invalid_excluded a [7,6,1,0,8,4,4] (by decide +kernel))
      node_2306
      (invalid_excluded a [7,6,1,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,8,4,8] (by decide +kernel)))

theorem node_2295 : Excluded a [7,6,1,0,8] :=
  branch_excluded a [7,6,1,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,1,0,8,0] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,8,1] (by decide +kernel))
      node_2296
      node_2297
      node_2303
      (invalid_excluded a [7,6,1,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,8,8] (by decide +kernel)))

theorem node_2273 : Excluded a [7,6,1,0] :=
  branch_excluded a [7,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,1] (by decide +kernel))
      node_2274
      node_2286
      (invalid_excluded a [7,6,1,0,4] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,0,7] (by decide +kernel))
      node_2295)

theorem node_2307 : Excluded a [7,6,1,2] :=
  predecessor_excluded a [7,6,1,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_2308 : Excluded a [7,6,1,5] :=
  source_excluded a [7,6,1,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2310 : Excluded a [7,6,1,8,0] :=
  predecessor_excluded a [7,6,1,8,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_2312 : Excluded a [7,6,1,8,2,0] :=
  predecessor_excluded a [7,6,1,8,2,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2313 : Excluded a [7,6,1,8,2,3] :=
  predecessor_excluded a [7,6,1,8,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_2315 : Excluded a [7,6,1,8,2,4,0] :=
  source_excluded a [7,6,1,8,2,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2316 : Excluded a [7,6,1,8,2,4,3] :=
  predecessor_excluded a [7,6,1,8,2,4,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_2317 : Excluded a [7,6,1,8,2,4,5] :=
  predecessor_excluded a [7,6,1,8,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2314 : Excluded a [7,6,1,8,2,4] :=
  branch_excluded a [7,6,1,8,2,4] (by decide)
    (fin9_cases _
      node_2315
      (invalid_excluded a [7,6,1,8,2,4,1] (by decide +kernel))
      (invalid_excluded a [7,6,1,8,2,4,2] (by decide +kernel))
      node_2316
      (invalid_excluded a [7,6,1,8,2,4,4] (by decide +kernel))
      node_2317
      (invalid_excluded a [7,6,1,8,2,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,8,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,1,8,2,4,8] (by decide +kernel)))

theorem node_2311 : Excluded a [7,6,1,8,2] :=
  branch_excluded a [7,6,1,8,2] (by decide)
    (fin9_cases _
      node_2312
      (invalid_excluded a [7,6,1,8,2,1] (by decide +kernel))
      (invalid_excluded a [7,6,1,8,2,2] (by decide +kernel))
      node_2313
      node_2314
      (invalid_excluded a [7,6,1,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,1,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,6,1,8,2,8] (by decide +kernel)))

theorem node_2319 : Excluded a [7,6,1,8,3,0] :=
  predecessor_excluded a [7,6,1,8,3,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2320 : Excluded a [7,6,1,8,3,2] :=
  source_excluded a [7,6,1,8,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2321 : Excluded a [7,6,1,8,3,4] :=
  predecessor_excluded a [7,6,1,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2318 : Excluded a [7,6,1,8,3] :=
  branch_excluded a [7,6,1,8,3] (by decide)
    (fin9_cases _
      node_2319
      (invalid_excluded a [7,6,1,8,3,1] (by decide +kernel))
      node_2320
      (invalid_excluded a [7,6,1,8,3,3] (by decide +kernel))
      node_2321
      (invalid_excluded a [7,6,1,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,6,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,1,8,3,8] (by decide +kernel)))

theorem node_2309 : Excluded a [7,6,1,8] :=
  branch_excluded a [7,6,1,8] (by decide)
    (fin9_cases _
      node_2310
      (invalid_excluded a [7,6,1,8,1] (by decide +kernel))
      node_2311
      node_2318
      (invalid_excluded a [7,6,1,8,4] (by decide +kernel))
      (invalid_excluded a [7,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,1,8,8] (by decide +kernel)))

theorem node_2272 : Excluded a [7,6,1] :=
  branch_excluded a [7,6,1] (by decide)
    (fin9_cases _
      node_2273
      (invalid_excluded a [7,6,1,1] (by decide +kernel))
      node_2307
      (invalid_excluded a [7,6,1,3] (by decide +kernel))
      (invalid_excluded a [7,6,1,4] (by decide +kernel))
      node_2308
      (invalid_excluded a [7,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,1,7] (by decide +kernel))
      node_2309)

theorem node_2322 : Excluded a [7,6,4] :=
  source_excluded a [7,6,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2325 : Excluded a [7,6,5,0,1] :=
  predecessor_excluded a [7,6,5,0,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2326 : Excluded a [7,6,5,0,2] :=
  source_excluded a [7,6,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2327 : Excluded a [7,6,5,0,3] :=
  source_excluded a [7,6,5,0,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2329 : Excluded a [7,6,5,0,8,1] :=
  source_excluded a [7,6,5,0,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2330 : Excluded a [7,6,5,0,8,2] :=
  source_excluded a [7,6,5,0,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2331 : Excluded a [7,6,5,0,8,3] :=
  source_excluded a [7,6,5,0,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2332 : Excluded a [7,6,5,0,8,4] :=
  predecessor_excluded a [7,6,5,0,8,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2328 : Excluded a [7,6,5,0,8] :=
  branch_excluded a [7,6,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,0,8,0] (by decide +kernel))
      node_2329
      node_2330
      node_2331
      node_2332
      (invalid_excluded a [7,6,5,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,8,8] (by decide +kernel)))

theorem node_2324 : Excluded a [7,6,5,0] :=
  branch_excluded a [7,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,0,0] (by decide +kernel))
      node_2325
      node_2326
      node_2327
      (invalid_excluded a [7,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,0,7] (by decide +kernel))
      node_2328)

theorem node_2335 : Excluded a [7,6,5,1,0,2] :=
  source_excluded a [7,6,5,1,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2336 : Excluded a [7,6,5,1,0,3] :=
  source_excluded a [7,6,5,1,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2337 : Excluded a [7,6,5,1,0,4] :=
  predecessor_excluded a [7,6,5,1,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2339 : Excluded a [7,6,5,1,0,8,2] :=
  source_excluded a [7,6,5,1,0,8,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2340 : Excluded a [7,6,5,1,0,8,3] :=
  predecessor_excluded a [7,6,5,1,0,8,3] 0 3 1 6 (by decide) (by decide +kernel)

theorem node_2342 : Excluded a [7,6,5,1,0,8,4,2] :=
  predecessor_excluded a [7,6,5,1,0,8,4,2] 3 2 0 7 (by decide) (by decide +kernel)

def b_2344 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 6
  | 2 => 5
  | 3 => 1
  | 4 => 0
  | 5 => 8
  | 6 => 4
  | 7 => 3
  | 8 => 2
  | _ => 0

def cert_2344 : LosingRegion (edgeOf a b_2344) 0 :=
  losingMask a b_2344 0 1210403001419417940718592
    (by decide +kernel) (by decide +kernel)

theorem node_2344 : Excluded a [7,6,5,1,0,8,4,3,2] :=
  losing_excluded a [7,6,5,1,0,8,4,3,2] (by decide) b_2344 (by decide +kernel) 1 0 3 cert_2344 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2344 1 0 ∧ 3 ≠ 1 ∧ maskRegion 1210403001419417940718592 1 3; decide +kernel)

theorem node_2343 : Excluded a [7,6,5,1,0,8,4,3] :=
  branch_excluded a [7,6,5,1,0,8,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,1,0,8,4,3,0] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,4,3,1] (by decide +kernel))
      node_2344
      (invalid_excluded a [7,6,5,1,0,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,4,3,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,4,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,4,3,8] (by decide +kernel)))

theorem node_2341 : Excluded a [7,6,5,1,0,8,4] :=
  branch_excluded a [7,6,5,1,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,1,0,8,4,0] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,4,1] (by decide +kernel))
      node_2342
      node_2343
      (invalid_excluded a [7,6,5,1,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,4,8] (by decide +kernel)))

theorem node_2338 : Excluded a [7,6,5,1,0,8] :=
  branch_excluded a [7,6,5,1,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,1,0,8,0] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,1] (by decide +kernel))
      node_2339
      node_2340
      node_2341
      (invalid_excluded a [7,6,5,1,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,8,8] (by decide +kernel)))

theorem node_2334 : Excluded a [7,6,5,1,0] :=
  branch_excluded a [7,6,5,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,5,1,0,0] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,1] (by decide +kernel))
      node_2335
      node_2336
      node_2337
      (invalid_excluded a [7,6,5,1,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,0,7] (by decide +kernel))
      node_2338)

theorem node_2345 : Excluded a [7,6,5,1,2] :=
  source_excluded a [7,6,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2346 : Excluded a [7,6,5,1,3] :=
  source_excluded a [7,6,5,1,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2348 : Excluded a [7,6,5,1,8,0] :=
  predecessor_excluded a [7,6,5,1,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2349 : Excluded a [7,6,5,1,8,2] :=
  source_excluded a [7,6,5,1,8,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2350 : Excluded a [7,6,5,1,8,3] :=
  source_excluded a [7,6,5,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2351 : Excluded a [7,6,5,1,8,4] :=
  predecessor_excluded a [7,6,5,1,8,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2347 : Excluded a [7,6,5,1,8] :=
  branch_excluded a [7,6,5,1,8] (by decide)
    (fin9_cases _
      node_2348
      (invalid_excluded a [7,6,5,1,8,1] (by decide +kernel))
      node_2349
      node_2350
      node_2351
      (invalid_excluded a [7,6,5,1,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,8,8] (by decide +kernel)))

theorem node_2333 : Excluded a [7,6,5,1] :=
  branch_excluded a [7,6,5,1] (by decide)
    (fin9_cases _
      node_2334
      (invalid_excluded a [7,6,5,1,1] (by decide +kernel))
      node_2345
      node_2346
      (invalid_excluded a [7,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,1,7] (by decide +kernel))
      node_2347)

theorem node_2352 : Excluded a [7,6,5,2] :=
  predecessor_excluded a [7,6,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_2354 : Excluded a [7,6,5,8,0] :=
  predecessor_excluded a [7,6,5,8,0] 1 0 3 4 (by decide) (by decide +kernel)

theorem node_2355 : Excluded a [7,6,5,8,1] :=
  predecessor_excluded a [7,6,5,8,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2356 : Excluded a [7,6,5,8,2] :=
  source_excluded a [7,6,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2357 : Excluded a [7,6,5,8,3] :=
  source_excluded a [7,6,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2353 : Excluded a [7,6,5,8] :=
  branch_excluded a [7,6,5,8] (by decide)
    (fin9_cases _
      node_2354
      node_2355
      node_2356
      node_2357
      (invalid_excluded a [7,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,5,8,8] (by decide +kernel)))

theorem node_2323 : Excluded a [7,6,5] :=
  branch_excluded a [7,6,5] (by decide)
    (fin9_cases _
      node_2324
      node_2333
      node_2352
      (invalid_excluded a [7,6,5,3] (by decide +kernel))
      (invalid_excluded a [7,6,5,4] (by decide +kernel))
      (invalid_excluded a [7,6,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,5,7] (by decide +kernel))
      node_2353)

theorem node_2359 : Excluded a [7,6,8,0] :=
  predecessor_excluded a [7,6,8,0] 1 0 2 3 (by decide) (by decide +kernel)

theorem node_2362 : Excluded a [7,6,8,1,0,2] :=
  source_excluded a [7,6,8,1,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2364 : Excluded a [7,6,8,1,0,3,2] :=
  source_excluded a [7,6,8,1,0,3,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2365 : Excluded a [7,6,8,1,0,3,4] :=
  predecessor_excluded a [7,6,8,1,0,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_2367 : Excluded a [7,6,8,1,0,3,5,2] :=
  source_excluded a [7,6,8,1,0,3,5,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_2368 : Excluded a [7,6,8,1,0,3,5,4] :=
  predecessor_excluded a [7,6,8,1,0,3,5,4] 1 0 7 4 (by decide) (by decide +kernel)

theorem node_2366 : Excluded a [7,6,8,1,0,3,5] :=
  branch_excluded a [7,6,8,1,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,3,5,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,5,1] (by decide +kernel))
      node_2367
      (invalid_excluded a [7,6,8,1,0,3,5,3] (by decide +kernel))
      node_2368
      (invalid_excluded a [7,6,8,1,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,5,8] (by decide +kernel)))

theorem node_2363 : Excluded a [7,6,8,1,0,3] :=
  branch_excluded a [7,6,8,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,1] (by decide +kernel))
      node_2364
      (invalid_excluded a [7,6,8,1,0,3,3] (by decide +kernel))
      node_2365
      node_2366
      (invalid_excluded a [7,6,8,1,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,3,8] (by decide +kernel)))

theorem node_2370 : Excluded a [7,6,8,1,0,4,2] :=
  source_excluded a [7,6,8,1,0,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2371 : Excluded a [7,6,8,1,0,4,3] :=
  predecessor_excluded a [7,6,8,1,0,4,3] 0 3 1 6 (by decide) (by decide +kernel)

theorem node_2372 : Excluded a [7,6,8,1,0,4,5] :=
  predecessor_excluded a [7,6,8,1,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2369 : Excluded a [7,6,8,1,0,4] :=
  branch_excluded a [7,6,8,1,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,4,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,1] (by decide +kernel))
      node_2370
      node_2371
      (invalid_excluded a [7,6,8,1,0,4,4] (by decide +kernel))
      node_2372
      (invalid_excluded a [7,6,8,1,0,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,4,8] (by decide +kernel)))

theorem node_2361 : Excluded a [7,6,8,1,0] :=
  branch_excluded a [7,6,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,1] (by decide +kernel))
      node_2362
      node_2363
      node_2369
      (invalid_excluded a [7,6,8,1,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,0,8] (by decide +kernel)))

theorem node_2373 : Excluded a [7,6,8,1,2] :=
  predecessor_excluded a [7,6,8,1,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_2375 : Excluded a [7,6,8,1,3,0] :=
  predecessor_excluded a [7,6,8,1,3,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2376 : Excluded a [7,6,8,1,3,2] :=
  source_excluded a [7,6,8,1,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2377 : Excluded a [7,6,8,1,3,4] :=
  predecessor_excluded a [7,6,8,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2374 : Excluded a [7,6,8,1,3] :=
  branch_excluded a [7,6,8,1,3] (by decide)
    (fin9_cases _
      node_2375
      (invalid_excluded a [7,6,8,1,3,1] (by decide +kernel))
      node_2376
      (invalid_excluded a [7,6,8,1,3,3] (by decide +kernel))
      node_2377
      (invalid_excluded a [7,6,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,3,8] (by decide +kernel)))

theorem node_2360 : Excluded a [7,6,8,1] :=
  branch_excluded a [7,6,8,1] (by decide)
    (fin9_cases _
      node_2361
      (invalid_excluded a [7,6,8,1,1] (by decide +kernel))
      node_2373
      node_2374
      (invalid_excluded a [7,6,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,1,8] (by decide +kernel)))

theorem node_2380 : Excluded a [7,6,8,2,0,1] :=
  source_excluded a [7,6,8,2,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2382 : Excluded a [7,6,8,2,0,3,1] :=
  source_excluded a [7,6,8,2,0,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2383 : Excluded a [7,6,8,2,0,3,4] :=
  predecessor_excluded a [7,6,8,2,0,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_2385 : Excluded a [7,6,8,2,0,3,5,1] :=
  source_excluded a [7,6,8,2,0,3,5,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2386 : Excluded a [7,6,8,2,0,3,5,4] :=
  predecessor_excluded a [7,6,8,2,0,3,5,4] 1 0 7 4 (by decide) (by decide +kernel)

theorem node_2384 : Excluded a [7,6,8,2,0,3,5] :=
  branch_excluded a [7,6,8,2,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,2,0,3,5,0] (by decide +kernel))
      node_2385
      (invalid_excluded a [7,6,8,2,0,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,0,3,5,3] (by decide +kernel))
      node_2386
      (invalid_excluded a [7,6,8,2,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,0,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,0,3,5,8] (by decide +kernel)))

theorem node_2381 : Excluded a [7,6,8,2,0,3] :=
  branch_excluded a [7,6,8,2,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,2,0,3,0] (by decide +kernel))
      node_2382
      (invalid_excluded a [7,6,8,2,0,3,2] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,0,3,3] (by decide +kernel))
      node_2383
      node_2384
      (invalid_excluded a [7,6,8,2,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,0,3,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,0,3,8] (by decide +kernel)))

theorem node_2388 : Excluded a [7,6,8,2,0,4,1] :=
  source_excluded a [7,6,8,2,0,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2389 : Excluded a [7,6,8,2,0,4,3] :=
  predecessor_excluded a [7,6,8,2,0,4,3] 0 3 1 6 (by decide) (by decide +kernel)

theorem node_2390 : Excluded a [7,6,8,2,0,4,5] :=
  predecessor_excluded a [7,6,8,2,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2387 : Excluded a [7,6,8,2,0,4] :=
  branch_excluded a [7,6,8,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,2,0,4,0] (by decide +kernel))
      node_2388
      (invalid_excluded a [7,6,8,2,0,4,2] (by decide +kernel))
      node_2389
      (invalid_excluded a [7,6,8,2,0,4,4] (by decide +kernel))
      node_2390
      (invalid_excluded a [7,6,8,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,0,4,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,0,4,8] (by decide +kernel)))

theorem node_2379 : Excluded a [7,6,8,2,0] :=
  branch_excluded a [7,6,8,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,6,8,2,0,0] (by decide +kernel))
      node_2380
      (invalid_excluded a [7,6,8,2,0,2] (by decide +kernel))
      node_2381
      node_2387
      (invalid_excluded a [7,6,8,2,0,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,0,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,0,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,0,8] (by decide +kernel)))

theorem node_2391 : Excluded a [7,6,8,2,1] :=
  predecessor_excluded a [7,6,8,2,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2392 : Excluded a [7,6,8,2,3] :=
  predecessor_excluded a [7,6,8,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2378 : Excluded a [7,6,8,2] :=
  branch_excluded a [7,6,8,2] (by decide)
    (fin9_cases _
      node_2379
      node_2391
      (invalid_excluded a [7,6,8,2,2] (by decide +kernel))
      node_2392
      (invalid_excluded a [7,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,2,8] (by decide +kernel)))

theorem node_2393 : Excluded a [7,6,8,5] :=
  source_excluded a [7,6,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2358 : Excluded a [7,6,8] :=
  branch_excluded a [7,6,8] (by decide)
    (fin9_cases _
      node_2359
      node_2360
      node_2378
      (invalid_excluded a [7,6,8,3] (by decide +kernel))
      (invalid_excluded a [7,6,8,4] (by decide +kernel))
      node_2393
      (invalid_excluded a [7,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,6,8,8] (by decide +kernel)))

theorem node_2240 : Excluded a [7,6] :=
  branch_excluded a [7,6] (by decide)
    (fin9_cases _
      node_2241
      node_2272
      (invalid_excluded a [7,6,2] (by decide +kernel))
      (invalid_excluded a [7,6,3] (by decide +kernel))
      node_2322
      node_2323
      (invalid_excluded a [7,6,6] (by decide +kernel))
      (invalid_excluded a [7,6,7] (by decide +kernel))
      node_2358)

theorem node_2394 : Excluded a [7,8] :=
  predecessor_excluded a [7,8] 2 8 0 1 (by decide) (by decide +kernel)

theorem node_1873 : Excluded a [7] :=
  branch_excluded a [7] (by decide)
    (fin9_cases _
      node_1874
      (invalid_excluded a [7,1] (by decide +kernel))
      (invalid_excluded a [7,2] (by decide +kernel))
      node_2016
      node_2017
      node_2109
      node_2240
      (invalid_excluded a [7,7] (by decide +kernel))
      node_2394)

theorem node_2396 : Excluded a [8,0] :=
  predecessor_excluded a [8,0] 2 0 0 1 (by decide) (by decide +kernel)

theorem node_2397 : Excluded a [8,3] :=
  source_excluded a [8,3] 1 0 2 (by decide) (by decide +kernel)

theorem node_2400 : Excluded a [8,4,0,1] :=
  source_excluded a [8,4,0,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2401 : Excluded a [8,4,0,2] :=
  source_excluded a [8,4,0,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_2402 : Excluded a [8,4,0,5] :=
  source_excluded a [8,4,0,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2405 : Excluded a [8,4,0,6,1,2] :=
  predecessor_excluded a [8,4,0,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2406 : Excluded a [8,4,0,6,1,3] :=
  source_excluded a [8,4,0,6,1,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2407 : Excluded a [8,4,0,6,1,7] :=
  source_excluded a [8,4,0,6,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2404 : Excluded a [8,4,0,6,1] :=
  branch_excluded a [8,4,0,6,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,6,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,1,1] (by decide +kernel))
      node_2405
      node_2406
      (invalid_excluded a [8,4,0,6,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,1,6] (by decide +kernel))
      node_2407
      (invalid_excluded a [8,4,0,6,1,8] (by decide +kernel)))

theorem node_2408 : Excluded a [8,4,0,6,2] :=
  source_excluded a [8,4,0,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2409 : Excluded a [8,4,0,6,3] :=
  predecessor_excluded a [8,4,0,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2410 : Excluded a [8,4,0,6,7] :=
  predecessor_excluded a [8,4,0,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_2403 : Excluded a [8,4,0,6] :=
  branch_excluded a [8,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,6,0] (by decide +kernel))
      node_2404
      node_2408
      node_2409
      (invalid_excluded a [8,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,6] (by decide +kernel))
      node_2410
      (invalid_excluded a [8,4,0,6,8] (by decide +kernel)))

theorem node_2413 : Excluded a [8,4,0,7,1,2] :=
  predecessor_excluded a [8,4,0,7,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2414 : Excluded a [8,4,0,7,1,3] :=
  predecessor_excluded a [8,4,0,7,1,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2412 : Excluded a [8,4,0,7,1] :=
  branch_excluded a [8,4,0,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,1,1] (by decide +kernel))
      node_2413
      node_2414
      (invalid_excluded a [8,4,0,7,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,1,8] (by decide +kernel)))

theorem node_2415 : Excluded a [8,4,0,7,2] :=
  source_excluded a [8,4,0,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2416 : Excluded a [8,4,0,7,3] :=
  predecessor_excluded a [8,4,0,7,3] 0 3 1 4 (by decide) (by decide +kernel)

theorem node_2417 : Excluded a [8,4,0,7,6] :=
  source_excluded a [8,4,0,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2411 : Excluded a [8,4,0,7] :=
  branch_excluded a [8,4,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,0] (by decide +kernel))
      node_2412
      node_2415
      node_2416
      (invalid_excluded a [8,4,0,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5] (by decide +kernel))
      node_2417
      (invalid_excluded a [8,4,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,8] (by decide +kernel)))

theorem node_2399 : Excluded a [8,4,0] :=
  branch_excluded a [8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,0] (by decide +kernel))
      node_2400
      node_2401
      (invalid_excluded a [8,4,0,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,4] (by decide +kernel))
      node_2402
      node_2403
      node_2411
      (invalid_excluded a [8,4,0,8] (by decide +kernel)))

theorem node_2418 : Excluded a [8,4,1] :=
  predecessor_excluded a [8,4,1] 0 4 2 1 (by decide) (by decide +kernel)

theorem node_2419 : Excluded a [8,4,5] :=
  predecessor_excluded a [8,4,5] 0 5 1 2 (by decide) (by decide +kernel)

theorem node_2422 : Excluded a [8,4,6,0,1] :=
  predecessor_excluded a [8,4,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2423 : Excluded a [8,4,6,0,2] :=
  source_excluded a [8,4,6,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2424 : Excluded a [8,4,6,0,3] :=
  predecessor_excluded a [8,4,6,0,3] 0 3 1 4 (by decide) (by decide +kernel)

theorem node_2427 : Excluded a [8,4,6,0,7,1,2] :=
  predecessor_excluded a [8,4,6,0,7,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2428 : Excluded a [8,4,6,0,7,1,3] :=
  source_excluded a [8,4,6,0,7,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2429 : Excluded a [8,4,6,0,7,1,5] :=
  source_excluded a [8,4,6,0,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2426 : Excluded a [8,4,6,0,7,1] :=
  branch_excluded a [8,4,6,0,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,7,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,1] (by decide +kernel))
      node_2427
      node_2428
      (invalid_excluded a [8,4,6,0,7,1,4] (by decide +kernel))
      node_2429
      (invalid_excluded a [8,4,6,0,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,1,8] (by decide +kernel)))

theorem node_2430 : Excluded a [8,4,6,0,7,2] :=
  source_excluded a [8,4,6,0,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2431 : Excluded a [8,4,6,0,7,3] :=
  source_excluded a [8,4,6,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2425 : Excluded a [8,4,6,0,7] :=
  branch_excluded a [8,4,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,7,0] (by decide +kernel))
      node_2426
      node_2430
      node_2431
      (invalid_excluded a [8,4,6,0,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,7,8] (by decide +kernel)))

theorem node_2421 : Excluded a [8,4,6,0] :=
  branch_excluded a [8,4,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,0,0] (by decide +kernel))
      node_2422
      node_2423
      node_2424
      (invalid_excluded a [8,4,6,0,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,0,6] (by decide +kernel))
      node_2425
      (invalid_excluded a [8,4,6,0,8] (by decide +kernel)))

theorem node_2432 : Excluded a [8,4,6,1] :=
  source_excluded a [8,4,6,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2433 : Excluded a [8,4,6,2] :=
  source_excluded a [8,4,6,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_2434 : Excluded a [8,4,6,5] :=
  source_excluded a [8,4,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2435 : Excluded a [8,4,6,7] :=
  predecessor_excluded a [8,4,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_2420 : Excluded a [8,4,6] :=
  branch_excluded a [8,4,6] (by decide)
    (fin9_cases _
      node_2421
      node_2432
      node_2433
      (invalid_excluded a [8,4,6,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,4] (by decide +kernel))
      node_2434
      (invalid_excluded a [8,4,6,6] (by decide +kernel))
      node_2435
      (invalid_excluded a [8,4,6,8] (by decide +kernel)))

theorem node_2438 : Excluded a [8,4,7,0,1] :=
  predecessor_excluded a [8,4,7,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2439 : Excluded a [8,4,7,0,2] :=
  source_excluded a [8,4,7,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2440 : Excluded a [8,4,7,0,3] :=
  predecessor_excluded a [8,4,7,0,3] 0 3 1 4 (by decide) (by decide +kernel)

theorem node_2441 : Excluded a [8,4,7,0,6] :=
  source_excluded a [8,4,7,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2437 : Excluded a [8,4,7,0] :=
  branch_excluded a [8,4,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,7,0,0] (by decide +kernel))
      node_2438
      node_2439
      node_2440
      (invalid_excluded a [8,4,7,0,4] (by decide +kernel))
      (invalid_excluded a [8,4,7,0,5] (by decide +kernel))
      node_2441
      (invalid_excluded a [8,4,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,0,8] (by decide +kernel)))

theorem node_2442 : Excluded a [8,4,7,1] :=
  source_excluded a [8,4,7,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2443 : Excluded a [8,4,7,2] :=
  source_excluded a [8,4,7,2] 1 0 3 (by decide) (by decide +kernel)

theorem node_2444 : Excluded a [8,4,7,5] :=
  source_excluded a [8,4,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2447 : Excluded a [8,4,7,6,0,1] :=
  predecessor_excluded a [8,4,7,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2448 : Excluded a [8,4,7,6,0,2] :=
  predecessor_excluded a [8,4,7,6,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_2449 : Excluded a [8,4,7,6,0,3] :=
  source_excluded a [8,4,7,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2446 : Excluded a [8,4,7,6,0] :=
  branch_excluded a [8,4,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,7,6,0,0] (by decide +kernel))
      node_2447
      node_2448
      node_2449
      (invalid_excluded a [8,4,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,0,8] (by decide +kernel)))

theorem node_2452 : Excluded a [8,4,7,6,1,0,2] :=
  source_excluded a [8,4,7,6,1,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_2453 : Excluded a [8,4,7,6,1,0,3] :=
  source_excluded a [8,4,7,6,1,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2454 : Excluded a [8,4,7,6,1,0,5] :=
  predecessor_excluded a [8,4,7,6,1,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2451 : Excluded a [8,4,7,6,1,0] :=
  branch_excluded a [8,4,7,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,7,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,1,0,1] (by decide +kernel))
      node_2452
      node_2453
      (invalid_excluded a [8,4,7,6,1,0,4] (by decide +kernel))
      node_2454
      (invalid_excluded a [8,4,7,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,1,0,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,1,0,8] (by decide +kernel)))

theorem node_2455 : Excluded a [8,4,7,6,1,2] :=
  predecessor_excluded a [8,4,7,6,1,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_2456 : Excluded a [8,4,7,6,1,3] :=
  source_excluded a [8,4,7,6,1,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2450 : Excluded a [8,4,7,6,1] :=
  branch_excluded a [8,4,7,6,1] (by decide)
    (fin9_cases _
      node_2451
      (invalid_excluded a [8,4,7,6,1,1] (by decide +kernel))
      node_2455
      node_2456
      (invalid_excluded a [8,4,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,1,8] (by decide +kernel)))

theorem node_2457 : Excluded a [8,4,7,6,2] :=
  source_excluded a [8,4,7,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2458 : Excluded a [8,4,7,6,3] :=
  predecessor_excluded a [8,4,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2445 : Excluded a [8,4,7,6] :=
  branch_excluded a [8,4,7,6] (by decide)
    (fin9_cases _
      node_2446
      node_2450
      node_2457
      node_2458
      (invalid_excluded a [8,4,7,6,4] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,5] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,8] (by decide +kernel)))

theorem node_2436 : Excluded a [8,4,7] :=
  branch_excluded a [8,4,7] (by decide)
    (fin9_cases _
      node_2437
      node_2442
      node_2443
      (invalid_excluded a [8,4,7,3] (by decide +kernel))
      (invalid_excluded a [8,4,7,4] (by decide +kernel))
      node_2444
      node_2445
      (invalid_excluded a [8,4,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,8] (by decide +kernel)))

theorem node_2398 : Excluded a [8,4] :=
  branch_excluded a [8,4] (by decide)
    (fin9_cases _
      node_2399
      node_2418
      (invalid_excluded a [8,4,2] (by decide +kernel))
      (invalid_excluded a [8,4,3] (by decide +kernel))
      (invalid_excluded a [8,4,4] (by decide +kernel))
      node_2419
      node_2420
      node_2436
      (invalid_excluded a [8,4,8] (by decide +kernel)))

theorem node_2461 : Excluded a [8,5,0,1] :=
  predecessor_excluded a [8,5,0,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_2463 : Excluded a [8,5,0,2,1] :=
  source_excluded a [8,5,0,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2464 : Excluded a [8,5,0,2,3] :=
  predecessor_excluded a [8,5,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2465 : Excluded a [8,5,0,2,6] :=
  source_excluded a [8,5,0,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2469 : Excluded a [8,5,0,2,7,1,3,4] :=
  predecessor_excluded a [8,5,0,2,7,1,3,4] 0 4 6 7 (by decide) (by decide +kernel)

theorem node_2470 : Excluded a [8,5,0,2,7,1,3,6] :=
  predecessor_excluded a [8,5,0,2,7,1,3,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_2468 : Excluded a [8,5,0,2,7,1,3] :=
  branch_excluded a [8,5,0,2,7,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,2,7,1,3,0] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,1,3,1] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,1,3,2] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,1,3,3] (by decide +kernel))
      node_2469
      (invalid_excluded a [8,5,0,2,7,1,3,5] (by decide +kernel))
      node_2470
      (invalid_excluded a [8,5,0,2,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,1,3,8] (by decide +kernel)))

theorem node_2471 : Excluded a [8,5,0,2,7,1,4] :=
  source_excluded a [8,5,0,2,7,1,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2467 : Excluded a [8,5,0,2,7,1] :=
  branch_excluded a [8,5,0,2,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,2,7,1,0] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,1,1] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,1,2] (by decide +kernel))
      node_2468
      node_2471
      (invalid_excluded a [8,5,0,2,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,1,8] (by decide +kernel)))

theorem node_2472 : Excluded a [8,5,0,2,7,3] :=
  predecessor_excluded a [8,5,0,2,7,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_2473 : Excluded a [8,5,0,2,7,4] :=
  predecessor_excluded a [8,5,0,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2466 : Excluded a [8,5,0,2,7] :=
  branch_excluded a [8,5,0,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,2,7,0] (by decide +kernel))
      node_2467
      (invalid_excluded a [8,5,0,2,7,2] (by decide +kernel))
      node_2472
      node_2473
      (invalid_excluded a [8,5,0,2,7,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,6] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,8] (by decide +kernel)))

theorem node_2462 : Excluded a [8,5,0,2] :=
  branch_excluded a [8,5,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,2,0] (by decide +kernel))
      node_2463
      (invalid_excluded a [8,5,0,2,2] (by decide +kernel))
      node_2464
      (invalid_excluded a [8,5,0,2,4] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,5] (by decide +kernel))
      node_2465
      node_2466
      (invalid_excluded a [8,5,0,2,8] (by decide +kernel)))

theorem node_2475 : Excluded a [8,5,0,6,1] :=
  source_excluded a [8,5,0,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2476 : Excluded a [8,5,0,6,2] :=
  source_excluded a [8,5,0,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2477 : Excluded a [8,5,0,6,3] :=
  predecessor_excluded a [8,5,0,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2478 : Excluded a [8,5,0,6,7] :=
  predecessor_excluded a [8,5,0,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_2474 : Excluded a [8,5,0,6] :=
  branch_excluded a [8,5,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,6,0] (by decide +kernel))
      node_2475
      node_2476
      node_2477
      (invalid_excluded a [8,5,0,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,0,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,6,6] (by decide +kernel))
      node_2478
      (invalid_excluded a [8,5,0,6,8] (by decide +kernel)))

theorem node_2480 : Excluded a [8,5,0,7,1] :=
  source_excluded a [8,5,0,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2481 : Excluded a [8,5,0,7,2] :=
  source_excluded a [8,5,0,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2484 : Excluded a [8,5,0,7,3,1,2] :=
  predecessor_excluded a [8,5,0,7,3,1,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2485 : Excluded a [8,5,0,7,3,1,4] :=
  source_excluded a [8,5,0,7,3,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2483 : Excluded a [8,5,0,7,3,1] :=
  branch_excluded a [8,5,0,7,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,7,3,1,0] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,1,1] (by decide +kernel))
      node_2484
      (invalid_excluded a [8,5,0,7,3,1,3] (by decide +kernel))
      node_2485
      (invalid_excluded a [8,5,0,7,3,1,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,1,6] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,1,8] (by decide +kernel)))

theorem node_2486 : Excluded a [8,5,0,7,3,2] :=
  source_excluded a [8,5,0,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2487 : Excluded a [8,5,0,7,3,4] :=
  predecessor_excluded a [8,5,0,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2482 : Excluded a [8,5,0,7,3] :=
  branch_excluded a [8,5,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,7,3,0] (by decide +kernel))
      node_2483
      node_2486
      (invalid_excluded a [8,5,0,7,3,3] (by decide +kernel))
      node_2487
      (invalid_excluded a [8,5,0,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,8] (by decide +kernel)))

theorem node_2488 : Excluded a [8,5,0,7,6] :=
  source_excluded a [8,5,0,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2479 : Excluded a [8,5,0,7] :=
  branch_excluded a [8,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,7,0] (by decide +kernel))
      node_2480
      node_2481
      node_2482
      (invalid_excluded a [8,5,0,7,4] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,5] (by decide +kernel))
      node_2488
      (invalid_excluded a [8,5,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,8] (by decide +kernel)))

theorem node_2460 : Excluded a [8,5,0] :=
  branch_excluded a [8,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,0] (by decide +kernel))
      node_2461
      node_2462
      (invalid_excluded a [8,5,0,3] (by decide +kernel))
      (invalid_excluded a [8,5,0,4] (by decide +kernel))
      (invalid_excluded a [8,5,0,5] (by decide +kernel))
      node_2474
      node_2479
      (invalid_excluded a [8,5,0,8] (by decide +kernel)))

theorem node_2491 : Excluded a [8,5,1,0,2] :=
  source_excluded a [8,5,1,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2493 : Excluded a [8,5,1,0,3,2] :=
  source_excluded a [8,5,1,0,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2494 : Excluded a [8,5,1,0,3,4] :=
  predecessor_excluded a [8,5,1,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2495 : Excluded a [8,5,1,0,3,7] :=
  source_excluded a [8,5,1,0,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2492 : Excluded a [8,5,1,0,3] :=
  branch_excluded a [8,5,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [8,5,1,0,3,1] (by decide +kernel))
      node_2493
      (invalid_excluded a [8,5,1,0,3,3] (by decide +kernel))
      node_2494
      (invalid_excluded a [8,5,1,0,3,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,0,3,6] (by decide +kernel))
      node_2495
      (invalid_excluded a [8,5,1,0,3,8] (by decide +kernel)))

theorem node_2496 : Excluded a [8,5,1,0,6] :=
  source_excluded a [8,5,1,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2498 : Excluded a [8,5,1,0,7,2] :=
  source_excluded a [8,5,1,0,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2499 : Excluded a [8,5,1,0,7,3] :=
  predecessor_excluded a [8,5,1,0,7,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_2500 : Excluded a [8,5,1,0,7,4] :=
  predecessor_excluded a [8,5,1,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2497 : Excluded a [8,5,1,0,7] :=
  branch_excluded a [8,5,1,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,1,0,7,0] (by decide +kernel))
      (invalid_excluded a [8,5,1,0,7,1] (by decide +kernel))
      node_2498
      node_2499
      node_2500
      (invalid_excluded a [8,5,1,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,5,1,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,0,7,8] (by decide +kernel)))

theorem node_2490 : Excluded a [8,5,1,0] :=
  branch_excluded a [8,5,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,5,1,0,1] (by decide +kernel))
      node_2491
      node_2492
      (invalid_excluded a [8,5,1,0,4] (by decide +kernel))
      (invalid_excluded a [8,5,1,0,5] (by decide +kernel))
      node_2496
      node_2497
      (invalid_excluded a [8,5,1,0,8] (by decide +kernel)))

theorem node_2501 : Excluded a [8,5,1,2] :=
  predecessor_excluded a [8,5,1,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_2504 : Excluded a [8,5,1,6,0,2] :=
  source_excluded a [8,5,1,6,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2505 : Excluded a [8,5,1,6,0,3] :=
  source_excluded a [8,5,1,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2506 : Excluded a [8,5,1,6,0,4] :=
  source_excluded a [8,5,1,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2507 : Excluded a [8,5,1,6,0,7] :=
  source_excluded a [8,5,1,6,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2503 : Excluded a [8,5,1,6,0] :=
  branch_excluded a [8,5,1,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,1,6,0,0] (by decide +kernel))
      (invalid_excluded a [8,5,1,6,0,1] (by decide +kernel))
      node_2504
      node_2505
      node_2506
      (invalid_excluded a [8,5,1,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,6,0,6] (by decide +kernel))
      node_2507
      (invalid_excluded a [8,5,1,6,0,8] (by decide +kernel)))

theorem node_2508 : Excluded a [8,5,1,6,2] :=
  source_excluded a [8,5,1,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2509 : Excluded a [8,5,1,6,3] :=
  predecessor_excluded a [8,5,1,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2510 : Excluded a [8,5,1,6,7] :=
  predecessor_excluded a [8,5,1,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_2502 : Excluded a [8,5,1,6] :=
  branch_excluded a [8,5,1,6] (by decide)
    (fin9_cases _
      node_2503
      (invalid_excluded a [8,5,1,6,1] (by decide +kernel))
      node_2508
      node_2509
      (invalid_excluded a [8,5,1,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,6,6] (by decide +kernel))
      node_2510
      (invalid_excluded a [8,5,1,6,8] (by decide +kernel)))

theorem node_2513 : Excluded a [8,5,1,7,0,2] :=
  source_excluded a [8,5,1,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2514 : Excluded a [8,5,1,7,0,3] :=
  predecessor_excluded a [8,5,1,7,0,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2517 : Excluded a [8,5,1,7,0,4,2,3] :=
  predecessor_excluded a [8,5,1,7,0,4,2,3] 0 3 6 7 (by decide) (by decide +kernel)

def b_2519 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 5
  | 2 => 1
  | 3 => 7
  | 4 => 0
  | 5 => 4
  | 6 => 2
  | 7 => 6
  | 8 => 3
  | _ => 0

def cert_2519 : LosingRegion (edgeOf a b_2519) 0 :=
  losingMask a b_2519 0 1212485340630740901198848
    (by decide +kernel) (by decide +kernel)

theorem node_2519 : Excluded a [8,5,1,7,0,4,2,6,3] :=
  losing_excluded a [8,5,1,7,0,4,2,6,3] (by decide) b_2519 (by decide +kernel) 1 0 2 cert_2519 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2519 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212485340630740901198848 1 2; decide +kernel)

theorem node_2518 : Excluded a [8,5,1,7,0,4,2,6] :=
  branch_excluded a [8,5,1,7,0,4,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,1,7,0,4,2,6,0] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,2,6,1] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,2,6,2] (by decide +kernel))
      node_2519
      (invalid_excluded a [8,5,1,7,0,4,2,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,2,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,2,6,6] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,2,6,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,2,6,8] (by decide +kernel)))

theorem node_2516 : Excluded a [8,5,1,7,0,4,2] :=
  branch_excluded a [8,5,1,7,0,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,1,7,0,4,2,0] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,2,1] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,2,2] (by decide +kernel))
      node_2517
      (invalid_excluded a [8,5,1,7,0,4,2,4] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,2,5] (by decide +kernel))
      node_2518
      (invalid_excluded a [8,5,1,7,0,4,2,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,2,8] (by decide +kernel)))

theorem node_2520 : Excluded a [8,5,1,7,0,4,3] :=
  source_excluded a [8,5,1,7,0,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2515 : Excluded a [8,5,1,7,0,4] :=
  branch_excluded a [8,5,1,7,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,1,7,0,4,0] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,1] (by decide +kernel))
      node_2516
      node_2520
      (invalid_excluded a [8,5,1,7,0,4,4] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,6] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,4,8] (by decide +kernel)))

theorem node_2512 : Excluded a [8,5,1,7,0] :=
  branch_excluded a [8,5,1,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,1,7,0,0] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,1] (by decide +kernel))
      node_2513
      node_2514
      node_2515
      (invalid_excluded a [8,5,1,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,0,8] (by decide +kernel)))

theorem node_2521 : Excluded a [8,5,1,7,2] :=
  source_excluded a [8,5,1,7,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2525 : Excluded a [8,5,1,7,3,0,2,4] :=
  source_excluded a [8,5,1,7,3,0,2,4] 3 0 7 (by decide) (by decide +kernel)

def b_2527 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 5
  | 2 => 1
  | 3 => 7
  | 4 => 3
  | 5 => 0
  | 6 => 2
  | 7 => 6
  | 8 => 4
  | _ => 0

def cert_2527 : LosingRegion (edgeOf a b_2527) 0 :=
  losingMask a b_2527 0 1212485628019065227076608
    (by decide +kernel) (by decide +kernel)

theorem node_2527 : Excluded a [8,5,1,7,3,0,2,6,4] :=
  losing_excluded a [8,5,1,7,3,0,2,6,4] (by decide) b_2527 (by decide +kernel) 1 0 4 cert_2527 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2527 1 0 ∧ 4 ≠ 1 ∧ maskRegion 1212485628019065227076608 1 4; decide +kernel)

theorem node_2526 : Excluded a [8,5,1,7,3,0,2,6] :=
  branch_excluded a [8,5,1,7,3,0,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,1,7,3,0,2,6,0] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,0,2,6,1] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,0,2,6,2] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,0,2,6,3] (by decide +kernel))
      node_2527
      (invalid_excluded a [8,5,1,7,3,0,2,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,0,2,6,6] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,0,2,6,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,0,2,6,8] (by decide +kernel)))

theorem node_2524 : Excluded a [8,5,1,7,3,0,2] :=
  branch_excluded a [8,5,1,7,3,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,1,7,3,0,2,0] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,0,2,1] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,0,2,2] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,0,2,3] (by decide +kernel))
      node_2525
      (invalid_excluded a [8,5,1,7,3,0,2,5] (by decide +kernel))
      node_2526
      (invalid_excluded a [8,5,1,7,3,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,0,2,8] (by decide +kernel)))

theorem node_2528 : Excluded a [8,5,1,7,3,0,4] :=
  source_excluded a [8,5,1,7,3,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2523 : Excluded a [8,5,1,7,3,0] :=
  branch_excluded a [8,5,1,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,1,7,3,0,0] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,0,1] (by decide +kernel))
      node_2524
      (invalid_excluded a [8,5,1,7,3,0,3] (by decide +kernel))
      node_2528
      (invalid_excluded a [8,5,1,7,3,0,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,0,8] (by decide +kernel)))

theorem node_2529 : Excluded a [8,5,1,7,3,2] :=
  source_excluded a [8,5,1,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2530 : Excluded a [8,5,1,7,3,4] :=
  predecessor_excluded a [8,5,1,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2522 : Excluded a [8,5,1,7,3] :=
  branch_excluded a [8,5,1,7,3] (by decide)
    (fin9_cases _
      node_2523
      (invalid_excluded a [8,5,1,7,3,1] (by decide +kernel))
      node_2529
      (invalid_excluded a [8,5,1,7,3,3] (by decide +kernel))
      node_2530
      (invalid_excluded a [8,5,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,8] (by decide +kernel)))

theorem node_2531 : Excluded a [8,5,1,7,6] :=
  source_excluded a [8,5,1,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2511 : Excluded a [8,5,1,7] :=
  branch_excluded a [8,5,1,7] (by decide)
    (fin9_cases _
      node_2512
      (invalid_excluded a [8,5,1,7,1] (by decide +kernel))
      node_2521
      node_2522
      (invalid_excluded a [8,5,1,7,4] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,5] (by decide +kernel))
      node_2531
      (invalid_excluded a [8,5,1,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,8] (by decide +kernel)))

theorem node_2489 : Excluded a [8,5,1] :=
  branch_excluded a [8,5,1] (by decide)
    (fin9_cases _
      node_2490
      (invalid_excluded a [8,5,1,1] (by decide +kernel))
      node_2501
      (invalid_excluded a [8,5,1,3] (by decide +kernel))
      (invalid_excluded a [8,5,1,4] (by decide +kernel))
      (invalid_excluded a [8,5,1,5] (by decide +kernel))
      node_2502
      node_2511
      (invalid_excluded a [8,5,1,8] (by decide +kernel)))

theorem node_2532 : Excluded a [8,5,4] :=
  source_excluded a [8,5,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2533 : Excluded a [8,5,6] :=
  predecessor_excluded a [8,5,6] 0 6 1 2 (by decide) (by decide +kernel)

theorem node_2536 : Excluded a [8,5,7,0,1] :=
  source_excluded a [8,5,7,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2537 : Excluded a [8,5,7,0,2] :=
  source_excluded a [8,5,7,0,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2540 : Excluded a [8,5,7,0,3,1,2] :=
  source_excluded a [8,5,7,0,3,1,2] 6 0 2 (by decide) (by decide +kernel)

def b_2543 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 5
  | 2 => 7
  | 3 => 0
  | 4 => 3
  | 5 => 1
  | 6 => 4
  | 7 => 2
  | 8 => 6
  | _ => 0

def cert_2543 : LosingRegion (edgeOf a b_2543) 0 :=
  losingMask a b_2543 0 1210109950151235489303552
    (by decide +kernel) (by decide +kernel)

theorem node_2543 : Excluded a [8,5,7,0,3,1,4,2,6] :=
  losing_excluded a [8,5,7,0,3,1,4,2,6] (by decide) b_2543 (by decide +kernel) 1 0 2 cert_2543 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2543 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1210109950151235489303552 1 2; decide +kernel)

theorem node_2542 : Excluded a [8,5,7,0,3,1,4,2] :=
  branch_excluded a [8,5,7,0,3,1,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,0,3,1,4,2,0] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,2,1] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,2,2] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,2,3] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,2,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,2,5] (by decide +kernel))
      node_2543
      (invalid_excluded a [8,5,7,0,3,1,4,2,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,2,8] (by decide +kernel)))

theorem node_2545 : Excluded a [8,5,7,0,3,1,4,6,2] :=
  predecessor_excluded a [8,5,7,0,3,1,4,6,2] 3 2 0 8 (by decide) (by decide +kernel)

theorem node_2544 : Excluded a [8,5,7,0,3,1,4,6] :=
  branch_excluded a [8,5,7,0,3,1,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,0,3,1,4,6,0] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,6,1] (by decide +kernel))
      node_2545
      (invalid_excluded a [8,5,7,0,3,1,4,6,3] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,6,6] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,6,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,6,8] (by decide +kernel)))

theorem node_2541 : Excluded a [8,5,7,0,3,1,4] :=
  branch_excluded a [8,5,7,0,3,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,0,3,1,4,0] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,1] (by decide +kernel))
      node_2542
      (invalid_excluded a [8,5,7,0,3,1,4,3] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,5] (by decide +kernel))
      node_2544
      (invalid_excluded a [8,5,7,0,3,1,4,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,4,8] (by decide +kernel)))

theorem node_2539 : Excluded a [8,5,7,0,3,1] :=
  branch_excluded a [8,5,7,0,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,0,3,1,0] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,1] (by decide +kernel))
      node_2540
      (invalid_excluded a [8,5,7,0,3,1,3] (by decide +kernel))
      node_2541
      (invalid_excluded a [8,5,7,0,3,1,5] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,6] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,1,8] (by decide +kernel)))

theorem node_2546 : Excluded a [8,5,7,0,3,2] :=
  source_excluded a [8,5,7,0,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2547 : Excluded a [8,5,7,0,3,4] :=
  predecessor_excluded a [8,5,7,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2538 : Excluded a [8,5,7,0,3] :=
  branch_excluded a [8,5,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,0,3,0] (by decide +kernel))
      node_2539
      node_2546
      (invalid_excluded a [8,5,7,0,3,3] (by decide +kernel))
      node_2547
      (invalid_excluded a [8,5,7,0,3,5] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,8] (by decide +kernel)))

theorem node_2548 : Excluded a [8,5,7,0,6] :=
  source_excluded a [8,5,7,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2535 : Excluded a [8,5,7,0] :=
  branch_excluded a [8,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,0,0] (by decide +kernel))
      node_2536
      node_2537
      node_2538
      (invalid_excluded a [8,5,7,0,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,5] (by decide +kernel))
      node_2548
      (invalid_excluded a [8,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,8] (by decide +kernel)))

theorem node_2549 : Excluded a [8,5,7,1] :=
  predecessor_excluded a [8,5,7,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_2552 : Excluded a [8,5,7,2,0,1] :=
  predecessor_excluded a [8,5,7,2,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2553 : Excluded a [8,5,7,2,0,3] :=
  predecessor_excluded a [8,5,7,2,0,3] 0 3 1 5 (by decide) (by decide +kernel)

theorem node_2556 : Excluded a [8,5,7,2,0,4,1,3] :=
  source_excluded a [8,5,7,2,0,4,1,3] 2 0 7 (by decide) (by decide +kernel)

def b_2558 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 5
  | 2 => 7
  | 3 => 2
  | 4 => 0
  | 5 => 4
  | 6 => 1
  | 7 => 6
  | 8 => 3
  | _ => 0

def cert_2558 : LosingRegion (edgeOf a b_2558) 0 :=
  losingMask a b_2558 0 1212485268573151147752448
    (by decide +kernel) (by decide +kernel)

theorem node_2558 : Excluded a [8,5,7,2,0,4,1,6,3] :=
  losing_excluded a [8,5,7,2,0,4,1,6,3] (by decide) b_2558 (by decide +kernel) 1 0 2 cert_2558 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2558 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212485268573151147752448 1 2; decide +kernel)

theorem node_2557 : Excluded a [8,5,7,2,0,4,1,6] :=
  branch_excluded a [8,5,7,2,0,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,2,0,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,4,1,6,2] (by decide +kernel))
      node_2558
      (invalid_excluded a [8,5,7,2,0,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,4,1,6,8] (by decide +kernel)))

theorem node_2555 : Excluded a [8,5,7,2,0,4,1] :=
  branch_excluded a [8,5,7,2,0,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,2,0,4,1,0] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,4,1,1] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,4,1,2] (by decide +kernel))
      node_2556
      (invalid_excluded a [8,5,7,2,0,4,1,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,4,1,5] (by decide +kernel))
      node_2557
      (invalid_excluded a [8,5,7,2,0,4,1,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,4,1,8] (by decide +kernel)))

theorem node_2559 : Excluded a [8,5,7,2,0,4,3] :=
  source_excluded a [8,5,7,2,0,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2554 : Excluded a [8,5,7,2,0,4] :=
  branch_excluded a [8,5,7,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,2,0,4,0] (by decide +kernel))
      node_2555
      (invalid_excluded a [8,5,7,2,0,4,2] (by decide +kernel))
      node_2559
      (invalid_excluded a [8,5,7,2,0,4,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,4,5] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,4,8] (by decide +kernel)))

theorem node_2551 : Excluded a [8,5,7,2,0] :=
  branch_excluded a [8,5,7,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,2,0,0] (by decide +kernel))
      node_2552
      (invalid_excluded a [8,5,7,2,0,2] (by decide +kernel))
      node_2553
      node_2554
      (invalid_excluded a [8,5,7,2,0,5] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,6] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,0,8] (by decide +kernel)))

theorem node_2560 : Excluded a [8,5,7,2,1] :=
  source_excluded a [8,5,7,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2561 : Excluded a [8,5,7,2,3] :=
  predecessor_excluded a [8,5,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2562 : Excluded a [8,5,7,2,6] :=
  source_excluded a [8,5,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2550 : Excluded a [8,5,7,2] :=
  branch_excluded a [8,5,7,2] (by decide)
    (fin9_cases _
      node_2551
      node_2560
      (invalid_excluded a [8,5,7,2,2] (by decide +kernel))
      node_2561
      (invalid_excluded a [8,5,7,2,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,5] (by decide +kernel))
      node_2562
      (invalid_excluded a [8,5,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,8] (by decide +kernel)))

theorem node_2565 : Excluded a [8,5,7,6,0,1] :=
  predecessor_excluded a [8,5,7,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2566 : Excluded a [8,5,7,6,0,2] :=
  source_excluded a [8,5,7,6,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2567 : Excluded a [8,5,7,6,0,3] :=
  source_excluded a [8,5,7,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2568 : Excluded a [8,5,7,6,0,4] :=
  source_excluded a [8,5,7,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2564 : Excluded a [8,5,7,6,0] :=
  branch_excluded a [8,5,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,6,0,0] (by decide +kernel))
      node_2565
      node_2566
      node_2567
      node_2568
      (invalid_excluded a [8,5,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,5,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [8,5,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,6,0,8] (by decide +kernel)))

theorem node_2569 : Excluded a [8,5,7,6,1] :=
  source_excluded a [8,5,7,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2570 : Excluded a [8,5,7,6,2] :=
  source_excluded a [8,5,7,6,2] 1 0 4 (by decide) (by decide +kernel)

theorem node_2571 : Excluded a [8,5,7,6,3] :=
  predecessor_excluded a [8,5,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2563 : Excluded a [8,5,7,6] :=
  branch_excluded a [8,5,7,6] (by decide)
    (fin9_cases _
      node_2564
      node_2569
      node_2570
      node_2571
      (invalid_excluded a [8,5,7,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,5,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,6,8] (by decide +kernel)))

theorem node_2534 : Excluded a [8,5,7] :=
  branch_excluded a [8,5,7] (by decide)
    (fin9_cases _
      node_2535
      node_2549
      node_2550
      (invalid_excluded a [8,5,7,3] (by decide +kernel))
      (invalid_excluded a [8,5,7,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,5] (by decide +kernel))
      node_2563
      (invalid_excluded a [8,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,8] (by decide +kernel)))

theorem node_2459 : Excluded a [8,5] :=
  branch_excluded a [8,5] (by decide)
    (fin9_cases _
      node_2460
      node_2489
      (invalid_excluded a [8,5,2] (by decide +kernel))
      (invalid_excluded a [8,5,3] (by decide +kernel))
      node_2532
      (invalid_excluded a [8,5,5] (by decide +kernel))
      node_2533
      node_2534
      (invalid_excluded a [8,5,8] (by decide +kernel)))

theorem node_2574 : Excluded a [8,6,0,1] :=
  predecessor_excluded a [8,6,0,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_2576 : Excluded a [8,6,0,2,1] :=
  predecessor_excluded a [8,6,0,2,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2577 : Excluded a [8,6,0,2,3] :=
  predecessor_excluded a [8,6,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2579 : Excluded a [8,6,0,2,7,1] :=
  source_excluded a [8,6,0,2,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2583 : Excluded a [8,6,0,2,7,3,1,4,5] :=
  predecessor_excluded a [8,6,0,2,7,3,1,4,5] 0 5 7 8 (by decide) (by decide +kernel)

theorem node_2582 : Excluded a [8,6,0,2,7,3,1,4] :=
  branch_excluded a [8,6,0,2,7,3,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,2,7,3,1,4,0] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,1,4,1] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,1,4,2] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,1,4,3] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,1,4,4] (by decide +kernel))
      node_2583
      (invalid_excluded a [8,6,0,2,7,3,1,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,1,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,1,4,8] (by decide +kernel)))

theorem node_2584 : Excluded a [8,6,0,2,7,3,1,5] :=
  source_excluded a [8,6,0,2,7,3,1,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_2581 : Excluded a [8,6,0,2,7,3,1] :=
  branch_excluded a [8,6,0,2,7,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,2,7,3,1,0] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,1,1] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,1,2] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,1,3] (by decide +kernel))
      node_2582
      node_2584
      (invalid_excluded a [8,6,0,2,7,3,1,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,1,8] (by decide +kernel)))

theorem node_2585 : Excluded a [8,6,0,2,7,3,4] :=
  source_excluded a [8,6,0,2,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2586 : Excluded a [8,6,0,2,7,3,5] :=
  source_excluded a [8,6,0,2,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2580 : Excluded a [8,6,0,2,7,3] :=
  branch_excluded a [8,6,0,2,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,2,7,3,0] (by decide +kernel))
      node_2581
      (invalid_excluded a [8,6,0,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,3] (by decide +kernel))
      node_2585
      node_2586
      (invalid_excluded a [8,6,0,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,8] (by decide +kernel)))

theorem node_2587 : Excluded a [8,6,0,2,7,4] :=
  predecessor_excluded a [8,6,0,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2578 : Excluded a [8,6,0,2,7] :=
  branch_excluded a [8,6,0,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,2,7,0] (by decide +kernel))
      node_2579
      (invalid_excluded a [8,6,0,2,7,2] (by decide +kernel))
      node_2580
      node_2587
      (invalid_excluded a [8,6,0,2,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,8] (by decide +kernel)))

theorem node_2575 : Excluded a [8,6,0,2] :=
  branch_excluded a [8,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,2,0] (by decide +kernel))
      node_2576
      (invalid_excluded a [8,6,0,2,2] (by decide +kernel))
      node_2577
      (invalid_excluded a [8,6,0,2,4] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,6] (by decide +kernel))
      node_2578
      (invalid_excluded a [8,6,0,2,8] (by decide +kernel)))

theorem node_2588 : Excluded a [8,6,0,5] :=
  source_excluded a [8,6,0,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2590 : Excluded a [8,6,0,7,1] :=
  predecessor_excluded a [8,6,0,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2592 : Excluded a [8,6,0,7,2,1] :=
  source_excluded a [8,6,0,7,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2593 : Excluded a [8,6,0,7,2,3] :=
  predecessor_excluded a [8,6,0,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

def b_2597 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 6
  | 2 => 0
  | 3 => 7
  | 4 => 2
  | 5 => 4
  | 6 => 1
  | 7 => 3
  | 8 => 5
  | _ => 0

def cert_2597 : LosingRegion (edgeOf a b_2597) 0 :=
  losingMask a b_2597 0 1212478209427440913099776
    (by decide +kernel) (by decide +kernel)

theorem node_2597 : Excluded a [8,6,0,7,2,4,1,3,5] :=
  losing_excluded a [8,6,0,7,2,4,1,3,5] (by decide) b_2597 (by decide +kernel) 1 0 2 cert_2597 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2597 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212478209427440913099776 1 2; decide +kernel)

theorem node_2596 : Excluded a [8,6,0,7,2,4,1,3] :=
  branch_excluded a [8,6,0,7,2,4,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,2,4,1,3,0] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,4,1,3,1] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,4,1,3,2] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,4,1,3,3] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,4,1,3,4] (by decide +kernel))
      node_2597
      (invalid_excluded a [8,6,0,7,2,4,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,4,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,4,1,3,8] (by decide +kernel)))

theorem node_2598 : Excluded a [8,6,0,7,2,4,1,5] :=
  predecessor_excluded a [8,6,0,7,2,4,1,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_2595 : Excluded a [8,6,0,7,2,4,1] :=
  branch_excluded a [8,6,0,7,2,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,2,4,1,0] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,4,1,1] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,4,1,2] (by decide +kernel))
      node_2596
      (invalid_excluded a [8,6,0,7,2,4,1,4] (by decide +kernel))
      node_2598
      (invalid_excluded a [8,6,0,7,2,4,1,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,4,1,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,4,1,8] (by decide +kernel)))

theorem node_2599 : Excluded a [8,6,0,7,2,4,3] :=
  source_excluded a [8,6,0,7,2,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2600 : Excluded a [8,6,0,7,2,4,5] :=
  predecessor_excluded a [8,6,0,7,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2594 : Excluded a [8,6,0,7,2,4] :=
  branch_excluded a [8,6,0,7,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,2,4,0] (by decide +kernel))
      node_2595
      (invalid_excluded a [8,6,0,7,2,4,2] (by decide +kernel))
      node_2599
      (invalid_excluded a [8,6,0,7,2,4,4] (by decide +kernel))
      node_2600
      (invalid_excluded a [8,6,0,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,4,8] (by decide +kernel)))

theorem node_2591 : Excluded a [8,6,0,7,2] :=
  branch_excluded a [8,6,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,2,0] (by decide +kernel))
      node_2592
      (invalid_excluded a [8,6,0,7,2,2] (by decide +kernel))
      node_2593
      node_2594
      (invalid_excluded a [8,6,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,8] (by decide +kernel)))

theorem node_2602 : Excluded a [8,6,0,7,3,1] :=
  source_excluded a [8,6,0,7,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2603 : Excluded a [8,6,0,7,3,2] :=
  source_excluded a [8,6,0,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2604 : Excluded a [8,6,0,7,3,4] :=
  predecessor_excluded a [8,6,0,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2601 : Excluded a [8,6,0,7,3] :=
  branch_excluded a [8,6,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,3,0] (by decide +kernel))
      node_2602
      node_2603
      (invalid_excluded a [8,6,0,7,3,3] (by decide +kernel))
      node_2604
      (invalid_excluded a [8,6,0,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,3,8] (by decide +kernel)))

theorem node_2589 : Excluded a [8,6,0,7] :=
  branch_excluded a [8,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,0] (by decide +kernel))
      node_2590
      node_2591
      node_2601
      (invalid_excluded a [8,6,0,7,4] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,8] (by decide +kernel)))

theorem node_2573 : Excluded a [8,6,0] :=
  branch_excluded a [8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,0] (by decide +kernel))
      node_2574
      node_2575
      (invalid_excluded a [8,6,0,3] (by decide +kernel))
      (invalid_excluded a [8,6,0,4] (by decide +kernel))
      node_2588
      (invalid_excluded a [8,6,0,6] (by decide +kernel))
      node_2589
      (invalid_excluded a [8,6,0,8] (by decide +kernel)))

theorem node_2608 : Excluded a [8,6,1,0,2,3] :=
  predecessor_excluded a [8,6,1,0,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_2610 : Excluded a [8,6,1,0,2,4,3] :=
  predecessor_excluded a [8,6,1,0,2,4,3] 0 3 1 6 (by decide) (by decide +kernel)

theorem node_2611 : Excluded a [8,6,1,0,2,4,5] :=
  predecessor_excluded a [8,6,1,0,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2609 : Excluded a [8,6,1,0,2,4] :=
  branch_excluded a [8,6,1,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,0,2,4,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,2,4,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,2,4,2] (by decide +kernel))
      node_2610
      (invalid_excluded a [8,6,1,0,2,4,4] (by decide +kernel))
      node_2611
      (invalid_excluded a [8,6,1,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,2,4,8] (by decide +kernel)))

theorem node_2612 : Excluded a [8,6,1,0,2,7] :=
  source_excluded a [8,6,1,0,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2607 : Excluded a [8,6,1,0,2] :=
  branch_excluded a [8,6,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,2,2] (by decide +kernel))
      node_2608
      node_2609
      (invalid_excluded a [8,6,1,0,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,2,6] (by decide +kernel))
      node_2612
      (invalid_excluded a [8,6,1,0,2,8] (by decide +kernel)))

theorem node_2614 : Excluded a [8,6,1,0,3,2] :=
  source_excluded a [8,6,1,0,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2615 : Excluded a [8,6,1,0,3,4] :=
  predecessor_excluded a [8,6,1,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2616 : Excluded a [8,6,1,0,3,7] :=
  source_excluded a [8,6,1,0,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2613 : Excluded a [8,6,1,0,3] :=
  branch_excluded a [8,6,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,3,1] (by decide +kernel))
      node_2614
      (invalid_excluded a [8,6,1,0,3,3] (by decide +kernel))
      node_2615
      (invalid_excluded a [8,6,1,0,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,3,6] (by decide +kernel))
      node_2616
      (invalid_excluded a [8,6,1,0,3,8] (by decide +kernel)))

theorem node_2618 : Excluded a [8,6,1,0,7,2] :=
  source_excluded a [8,6,1,0,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2620 : Excluded a [8,6,1,0,7,3,2] :=
  source_excluded a [8,6,1,0,7,3,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2621 : Excluded a [8,6,1,0,7,3,4] :=
  source_excluded a [8,6,1,0,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2622 : Excluded a [8,6,1,0,7,3,5] :=
  source_excluded a [8,6,1,0,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2619 : Excluded a [8,6,1,0,7,3] :=
  branch_excluded a [8,6,1,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,0,7,3,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,7,3,1] (by decide +kernel))
      node_2620
      (invalid_excluded a [8,6,1,0,7,3,3] (by decide +kernel))
      node_2621
      node_2622
      (invalid_excluded a [8,6,1,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,7,3,8] (by decide +kernel)))

theorem node_2623 : Excluded a [8,6,1,0,7,4] :=
  predecessor_excluded a [8,6,1,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2617 : Excluded a [8,6,1,0,7] :=
  branch_excluded a [8,6,1,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,0,7,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,7,1] (by decide +kernel))
      node_2618
      node_2619
      node_2623
      (invalid_excluded a [8,6,1,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,7,8] (by decide +kernel)))

theorem node_2606 : Excluded a [8,6,1,0] :=
  branch_excluded a [8,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,1] (by decide +kernel))
      node_2607
      node_2613
      (invalid_excluded a [8,6,1,0,4] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,0,6] (by decide +kernel))
      node_2617
      (invalid_excluded a [8,6,1,0,8] (by decide +kernel)))

theorem node_2624 : Excluded a [8,6,1,2] :=
  predecessor_excluded a [8,6,1,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_2625 : Excluded a [8,6,1,5] :=
  source_excluded a [8,6,1,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2628 : Excluded a [8,6,1,7,0,2] :=
  source_excluded a [8,6,1,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2629 : Excluded a [8,6,1,7,0,3] :=
  predecessor_excluded a [8,6,1,7,0,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2631 : Excluded a [8,6,1,7,0,4,2] :=
  source_excluded a [8,6,1,7,0,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2632 : Excluded a [8,6,1,7,0,4,3] :=
  source_excluded a [8,6,1,7,0,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2633 : Excluded a [8,6,1,7,0,4,5] :=
  predecessor_excluded a [8,6,1,7,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2630 : Excluded a [8,6,1,7,0,4] :=
  branch_excluded a [8,6,1,7,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,7,0,4,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,4,1] (by decide +kernel))
      node_2631
      node_2632
      (invalid_excluded a [8,6,1,7,0,4,4] (by decide +kernel))
      node_2633
      (invalid_excluded a [8,6,1,7,0,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,4,8] (by decide +kernel)))

theorem node_2627 : Excluded a [8,6,1,7,0] :=
  branch_excluded a [8,6,1,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,7,0,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,1] (by decide +kernel))
      node_2628
      node_2629
      node_2630
      (invalid_excluded a [8,6,1,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,8] (by decide +kernel)))

theorem node_2636 : Excluded a [8,6,1,7,2,0,3] :=
  source_excluded a [8,6,1,7,2,0,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2637 : Excluded a [8,6,1,7,2,0,4] :=
  source_excluded a [8,6,1,7,2,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2640 : Excluded a [8,6,1,7,2,0,5,3,4] :=
  predecessor_excluded a [8,6,1,7,2,0,5,3,4] 0 4 7 8 (by decide) (by decide +kernel)

theorem node_2639 : Excluded a [8,6,1,7,2,0,5,3] :=
  branch_excluded a [8,6,1,7,2,0,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,7,2,0,5,3,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,5,3,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,5,3,2] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,5,3,3] (by decide +kernel))
      node_2640
      (invalid_excluded a [8,6,1,7,2,0,5,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,5,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,5,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,5,3,8] (by decide +kernel)))

theorem node_2641 : Excluded a [8,6,1,7,2,0,5,4] :=
  source_excluded a [8,6,1,7,2,0,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_2638 : Excluded a [8,6,1,7,2,0,5] :=
  branch_excluded a [8,6,1,7,2,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,7,2,0,5,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,5,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,5,2] (by decide +kernel))
      node_2639
      node_2641
      (invalid_excluded a [8,6,1,7,2,0,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,5,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,5,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,5,8] (by decide +kernel)))

theorem node_2635 : Excluded a [8,6,1,7,2,0] :=
  branch_excluded a [8,6,1,7,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,7,2,0,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,2] (by decide +kernel))
      node_2636
      node_2637
      node_2638
      (invalid_excluded a [8,6,1,7,2,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,0,8] (by decide +kernel)))

theorem node_2642 : Excluded a [8,6,1,7,2,3] :=
  predecessor_excluded a [8,6,1,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2644 : Excluded a [8,6,1,7,2,4,0] :=
  predecessor_excluded a [8,6,1,7,2,4,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2645 : Excluded a [8,6,1,7,2,4,3] :=
  source_excluded a [8,6,1,7,2,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2646 : Excluded a [8,6,1,7,2,4,5] :=
  predecessor_excluded a [8,6,1,7,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2643 : Excluded a [8,6,1,7,2,4] :=
  branch_excluded a [8,6,1,7,2,4] (by decide)
    (fin9_cases _
      node_2644
      (invalid_excluded a [8,6,1,7,2,4,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,4,2] (by decide +kernel))
      node_2645
      (invalid_excluded a [8,6,1,7,2,4,4] (by decide +kernel))
      node_2646
      (invalid_excluded a [8,6,1,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,4,8] (by decide +kernel)))

theorem node_2634 : Excluded a [8,6,1,7,2] :=
  branch_excluded a [8,6,1,7,2] (by decide)
    (fin9_cases _
      node_2635
      (invalid_excluded a [8,6,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,2] (by decide +kernel))
      node_2642
      node_2643
      (invalid_excluded a [8,6,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,8] (by decide +kernel)))

theorem node_2649 : Excluded a [8,6,1,7,3,0,2] :=
  source_excluded a [8,6,1,7,3,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2650 : Excluded a [8,6,1,7,3,0,4] :=
  source_excluded a [8,6,1,7,3,0,4] 3 0 6 (by decide) (by decide +kernel)

def b_2653 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 6
  | 2 => 1
  | 3 => 7
  | 4 => 3
  | 5 => 0
  | 6 => 5
  | 7 => 2
  | 8 => 4
  | _ => 0

def cert_2653 : LosingRegion (edgeOf a b_2653) 0 :=
  losingMask a b_2653 0 1212478548364720080741376
    (by decide +kernel) (by decide +kernel)

theorem node_2653 : Excluded a [8,6,1,7,3,0,5,2,4] :=
  losing_excluded a [8,6,1,7,3,0,5,2,4] (by decide) b_2653 (by decide +kernel) 1 0 4 cert_2653 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2653 1 0 ∧ 4 ≠ 1 ∧ maskRegion 1212478548364720080741376 1 4; decide +kernel)

theorem node_2652 : Excluded a [8,6,1,7,3,0,5,2] :=
  branch_excluded a [8,6,1,7,3,0,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,7,3,0,5,2,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,0,5,2,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,0,5,2,2] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,0,5,2,3] (by decide +kernel))
      node_2653
      (invalid_excluded a [8,6,1,7,3,0,5,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,0,5,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,0,5,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,0,5,2,8] (by decide +kernel)))

theorem node_2654 : Excluded a [8,6,1,7,3,0,5,4] :=
  source_excluded a [8,6,1,7,3,0,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_2651 : Excluded a [8,6,1,7,3,0,5] :=
  branch_excluded a [8,6,1,7,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,7,3,0,5,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,0,5,1] (by decide +kernel))
      node_2652
      (invalid_excluded a [8,6,1,7,3,0,5,3] (by decide +kernel))
      node_2654
      (invalid_excluded a [8,6,1,7,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,0,5,8] (by decide +kernel)))

theorem node_2648 : Excluded a [8,6,1,7,3,0] :=
  branch_excluded a [8,6,1,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,7,3,0,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,0,1] (by decide +kernel))
      node_2649
      (invalid_excluded a [8,6,1,7,3,0,3] (by decide +kernel))
      node_2650
      node_2651
      (invalid_excluded a [8,6,1,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,0,8] (by decide +kernel)))

theorem node_2655 : Excluded a [8,6,1,7,3,2] :=
  source_excluded a [8,6,1,7,3,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2656 : Excluded a [8,6,1,7,3,4] :=
  predecessor_excluded a [8,6,1,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2647 : Excluded a [8,6,1,7,3] :=
  branch_excluded a [8,6,1,7,3] (by decide)
    (fin9_cases _
      node_2648
      (invalid_excluded a [8,6,1,7,3,1] (by decide +kernel))
      node_2655
      (invalid_excluded a [8,6,1,7,3,3] (by decide +kernel))
      node_2656
      (invalid_excluded a [8,6,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,8] (by decide +kernel)))

theorem node_2626 : Excluded a [8,6,1,7] :=
  branch_excluded a [8,6,1,7] (by decide)
    (fin9_cases _
      node_2627
      (invalid_excluded a [8,6,1,7,1] (by decide +kernel))
      node_2634
      node_2647
      (invalid_excluded a [8,6,1,7,4] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,8] (by decide +kernel)))

theorem node_2605 : Excluded a [8,6,1] :=
  branch_excluded a [8,6,1] (by decide)
    (fin9_cases _
      node_2606
      (invalid_excluded a [8,6,1,1] (by decide +kernel))
      node_2624
      (invalid_excluded a [8,6,1,3] (by decide +kernel))
      (invalid_excluded a [8,6,1,4] (by decide +kernel))
      node_2625
      (invalid_excluded a [8,6,1,6] (by decide +kernel))
      node_2626
      (invalid_excluded a [8,6,1,8] (by decide +kernel)))

theorem node_2657 : Excluded a [8,6,4] :=
  source_excluded a [8,6,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2660 : Excluded a [8,6,5,0,1] :=
  predecessor_excluded a [8,6,5,0,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2661 : Excluded a [8,6,5,0,2] :=
  source_excluded a [8,6,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2662 : Excluded a [8,6,5,0,3] :=
  source_excluded a [8,6,5,0,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2664 : Excluded a [8,6,5,0,7,1] :=
  source_excluded a [8,6,5,0,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2665 : Excluded a [8,6,5,0,7,2] :=
  source_excluded a [8,6,5,0,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2666 : Excluded a [8,6,5,0,7,3] :=
  source_excluded a [8,6,5,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2667 : Excluded a [8,6,5,0,7,4] :=
  predecessor_excluded a [8,6,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2663 : Excluded a [8,6,5,0,7] :=
  branch_excluded a [8,6,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,0,7,0] (by decide +kernel))
      node_2664
      node_2665
      node_2666
      node_2667
      (invalid_excluded a [8,6,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,8] (by decide +kernel)))

theorem node_2659 : Excluded a [8,6,5,0] :=
  branch_excluded a [8,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,0,0] (by decide +kernel))
      node_2660
      node_2661
      node_2662
      (invalid_excluded a [8,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,6] (by decide +kernel))
      node_2663
      (invalid_excluded a [8,6,5,0,8] (by decide +kernel)))

theorem node_2670 : Excluded a [8,6,5,1,0,2] :=
  source_excluded a [8,6,5,1,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2671 : Excluded a [8,6,5,1,0,3] :=
  source_excluded a [8,6,5,1,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2672 : Excluded a [8,6,5,1,0,4] :=
  predecessor_excluded a [8,6,5,1,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2673 : Excluded a [8,6,5,1,0,7] :=
  source_excluded a [8,6,5,1,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2669 : Excluded a [8,6,5,1,0] :=
  branch_excluded a [8,6,5,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,0,1] (by decide +kernel))
      node_2670
      node_2671
      node_2672
      (invalid_excluded a [8,6,5,1,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,0,6] (by decide +kernel))
      node_2673
      (invalid_excluded a [8,6,5,1,0,8] (by decide +kernel)))

theorem node_2674 : Excluded a [8,6,5,1,2] :=
  source_excluded a [8,6,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2675 : Excluded a [8,6,5,1,3] :=
  source_excluded a [8,6,5,1,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2678 : Excluded a [8,6,5,1,7,0,2] :=
  source_excluded a [8,6,5,1,7,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2679 : Excluded a [8,6,5,1,7,0,3] :=
  predecessor_excluded a [8,6,5,1,7,0,3] 0 3 1 6 (by decide) (by decide +kernel)

theorem node_2680 : Excluded a [8,6,5,1,7,0,4] :=
  source_excluded a [8,6,5,1,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2677 : Excluded a [8,6,5,1,7,0] :=
  branch_excluded a [8,6,5,1,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,1,7,0,0] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,0,1] (by decide +kernel))
      node_2678
      node_2679
      node_2680
      (invalid_excluded a [8,6,5,1,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,0,8] (by decide +kernel)))

theorem node_2681 : Excluded a [8,6,5,1,7,2] :=
  source_excluded a [8,6,5,1,7,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2682 : Excluded a [8,6,5,1,7,3] :=
  source_excluded a [8,6,5,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2683 : Excluded a [8,6,5,1,7,4] :=
  predecessor_excluded a [8,6,5,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2676 : Excluded a [8,6,5,1,7] :=
  branch_excluded a [8,6,5,1,7] (by decide)
    (fin9_cases _
      node_2677
      (invalid_excluded a [8,6,5,1,7,1] (by decide +kernel))
      node_2681
      node_2682
      node_2683
      (invalid_excluded a [8,6,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,8] (by decide +kernel)))

theorem node_2668 : Excluded a [8,6,5,1] :=
  branch_excluded a [8,6,5,1] (by decide)
    (fin9_cases _
      node_2669
      (invalid_excluded a [8,6,5,1,1] (by decide +kernel))
      node_2674
      node_2675
      (invalid_excluded a [8,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,6] (by decide +kernel))
      node_2676
      (invalid_excluded a [8,6,5,1,8] (by decide +kernel)))

theorem node_2684 : Excluded a [8,6,5,2] :=
  predecessor_excluded a [8,6,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_2687 : Excluded a [8,6,5,7,0,1] :=
  source_excluded a [8,6,5,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_2688 : Excluded a [8,6,5,7,0,2] :=
  source_excluded a [8,6,5,7,0,2] 1 0 5 (by decide) (by decide +kernel)

theorem node_2689 : Excluded a [8,6,5,7,0,3] :=
  source_excluded a [8,6,5,7,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2690 : Excluded a [8,6,5,7,0,4] :=
  predecessor_excluded a [8,6,5,7,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2686 : Excluded a [8,6,5,7,0] :=
  branch_excluded a [8,6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,7,0,0] (by decide +kernel))
      node_2687
      node_2688
      node_2689
      node_2690
      (invalid_excluded a [8,6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,8] (by decide +kernel)))

theorem node_2691 : Excluded a [8,6,5,7,1] :=
  predecessor_excluded a [8,6,5,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_2692 : Excluded a [8,6,5,7,2] :=
  source_excluded a [8,6,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2693 : Excluded a [8,6,5,7,3] :=
  source_excluded a [8,6,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2685 : Excluded a [8,6,5,7] :=
  branch_excluded a [8,6,5,7] (by decide)
    (fin9_cases _
      node_2686
      node_2691
      node_2692
      node_2693
      (invalid_excluded a [8,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,8] (by decide +kernel)))

theorem node_2658 : Excluded a [8,6,5] :=
  branch_excluded a [8,6,5] (by decide)
    (fin9_cases _
      node_2659
      node_2668
      node_2684
      (invalid_excluded a [8,6,5,3] (by decide +kernel))
      (invalid_excluded a [8,6,5,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,6] (by decide +kernel))
      node_2685
      (invalid_excluded a [8,6,5,8] (by decide +kernel)))

theorem node_2694 : Excluded a [8,6,7] :=
  predecessor_excluded a [8,6,7] 0 7 1 2 (by decide) (by decide +kernel)

theorem node_2572 : Excluded a [8,6] :=
  branch_excluded a [8,6] (by decide)
    (fin9_cases _
      node_2573
      node_2605
      (invalid_excluded a [8,6,2] (by decide +kernel))
      (invalid_excluded a [8,6,3] (by decide +kernel))
      node_2657
      node_2658
      (invalid_excluded a [8,6,6] (by decide +kernel))
      node_2694
      (invalid_excluded a [8,6,8] (by decide +kernel)))

theorem node_2697 : Excluded a [8,7,0,1] :=
  predecessor_excluded a [8,7,0,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_2701 : Excluded a [8,7,0,2,1,3,4] :=
  predecessor_excluded a [8,7,0,2,1,3,4] 0 4 5 6 (by decide) (by decide +kernel)

def b_2704 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 5
  | 7 => 4
  | 8 => 6
  | _ => 0

def cert_2704 : LosingRegion (edgeOf a b_2704) 0 :=
  losingMask a b_2704 0 1212485016618887703170048
    (by decide +kernel) (by decide +kernel)

theorem node_2704 : Excluded a [8,7,0,2,1,3,5,4,6] :=
  losing_excluded a [8,7,0,2,1,3,5,4,6] (by decide) b_2704 (by decide +kernel) 1 0 2 cert_2704 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2704 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212485016618887703170048 1 2; decide +kernel)

theorem node_2703 : Excluded a [8,7,0,2,1,3,5,4] :=
  branch_excluded a [8,7,0,2,1,3,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0,2,1,3,5,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,5,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,5,4,2] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,5,4,3] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,5,4,5] (by decide +kernel))
      node_2704
      (invalid_excluded a [8,7,0,2,1,3,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,5,4,8] (by decide +kernel)))

theorem node_2705 : Excluded a [8,7,0,2,1,3,5,6] :=
  predecessor_excluded a [8,7,0,2,1,3,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_2702 : Excluded a [8,7,0,2,1,3,5] :=
  branch_excluded a [8,7,0,2,1,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0,2,1,3,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,5,3] (by decide +kernel))
      node_2703
      (invalid_excluded a [8,7,0,2,1,3,5,5] (by decide +kernel))
      node_2705
      (invalid_excluded a [8,7,0,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,5,8] (by decide +kernel)))

theorem node_2700 : Excluded a [8,7,0,2,1,3] :=
  branch_excluded a [8,7,0,2,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0,2,1,3,0] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,3] (by decide +kernel))
      node_2701
      node_2702
      (invalid_excluded a [8,7,0,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,3,8] (by decide +kernel)))

theorem node_2709 : Excluded a [8,7,0,2,1,4,3,5,6] :=
  predecessor_excluded a [8,7,0,2,1,4,3,5,6] 0 6 7 8 (by decide) (by decide +kernel)

theorem node_2708 : Excluded a [8,7,0,2,1,4,3,5] :=
  branch_excluded a [8,7,0,2,1,4,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0,2,1,4,3,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,5,2] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,5,3] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,5,4] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,5,5] (by decide +kernel))
      node_2709
      (invalid_excluded a [8,7,0,2,1,4,3,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,5,8] (by decide +kernel)))

def b_2711 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | 5 => 4
  | 6 => 3
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_2711 : LosingRegion (edgeOf a b_2711) 0 :=
  losingMask a b_2711 0 1212478110348859130514432
    (by decide +kernel) (by decide +kernel)

theorem node_2711 : Excluded a [8,7,0,2,1,4,3,6,5] :=
  losing_excluded a [8,7,0,2,1,4,3,6,5] (by decide) b_2711 (by decide +kernel) 1 0 2 cert_2711 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2711 1 0 ∧ 2 ≠ 1 ∧ maskRegion 1212478110348859130514432 1 2; decide +kernel)

theorem node_2710 : Excluded a [8,7,0,2,1,4,3,6] :=
  branch_excluded a [8,7,0,2,1,4,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0,2,1,4,3,6,0] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,6,1] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,6,2] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,6,4] (by decide +kernel))
      node_2711
      (invalid_excluded a [8,7,0,2,1,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,6,8] (by decide +kernel)))

theorem node_2707 : Excluded a [8,7,0,2,1,4,3] :=
  branch_excluded a [8,7,0,2,1,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0,2,1,4,3,0] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,1] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,3] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,4] (by decide +kernel))
      node_2708
      node_2710
      (invalid_excluded a [8,7,0,2,1,4,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,3,8] (by decide +kernel)))

theorem node_2712 : Excluded a [8,7,0,2,1,4,5] :=
  predecessor_excluded a [8,7,0,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2706 : Excluded a [8,7,0,2,1,4] :=
  branch_excluded a [8,7,0,2,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0,2,1,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,2] (by decide +kernel))
      node_2707
      (invalid_excluded a [8,7,0,2,1,4,4] (by decide +kernel))
      node_2712
      (invalid_excluded a [8,7,0,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,4,8] (by decide +kernel)))

theorem node_2699 : Excluded a [8,7,0,2,1] :=
  branch_excluded a [8,7,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,2] (by decide +kernel))
      node_2700
      node_2706
      (invalid_excluded a [8,7,0,2,1,5] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,1,8] (by decide +kernel)))

theorem node_2713 : Excluded a [8,7,0,2,3] :=
  predecessor_excluded a [8,7,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2714 : Excluded a [8,7,0,2,6] :=
  source_excluded a [8,7,0,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2698 : Excluded a [8,7,0,2] :=
  branch_excluded a [8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0,2,0] (by decide +kernel))
      node_2699
      (invalid_excluded a [8,7,0,2,2] (by decide +kernel))
      node_2713
      (invalid_excluded a [8,7,0,2,4] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,5] (by decide +kernel))
      node_2714
      (invalid_excluded a [8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,0,2,8] (by decide +kernel)))

theorem node_2715 : Excluded a [8,7,0,5] :=
  source_excluded a [8,7,0,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2718 : Excluded a [8,7,0,6,1,2] :=
  predecessor_excluded a [8,7,0,6,1,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2719 : Excluded a [8,7,0,6,1,3] :=
  source_excluded a [8,7,0,6,1,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2720 : Excluded a [8,7,0,6,1,4] :=
  source_excluded a [8,7,0,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2717 : Excluded a [8,7,0,6,1] :=
  branch_excluded a [8,7,0,6,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0,6,1,0] (by decide +kernel))
      (invalid_excluded a [8,7,0,6,1,1] (by decide +kernel))
      node_2718
      node_2719
      node_2720
      (invalid_excluded a [8,7,0,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,7,0,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,0,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,0,6,1,8] (by decide +kernel)))

theorem node_2722 : Excluded a [8,7,0,6,2,1] :=
  predecessor_excluded a [8,7,0,6,2,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_2723 : Excluded a [8,7,0,6,2,3] :=
  source_excluded a [8,7,0,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2724 : Excluded a [8,7,0,6,2,4] :=
  source_excluded a [8,7,0,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2721 : Excluded a [8,7,0,6,2] :=
  branch_excluded a [8,7,0,6,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0,6,2,0] (by decide +kernel))
      node_2722
      (invalid_excluded a [8,7,0,6,2,2] (by decide +kernel))
      node_2723
      node_2724
      (invalid_excluded a [8,7,0,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,7,0,6,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,0,6,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,0,6,2,8] (by decide +kernel)))

theorem node_2725 : Excluded a [8,7,0,6,3] :=
  predecessor_excluded a [8,7,0,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2716 : Excluded a [8,7,0,6] :=
  branch_excluded a [8,7,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0,6,0] (by decide +kernel))
      node_2717
      node_2721
      node_2725
      (invalid_excluded a [8,7,0,6,4] (by decide +kernel))
      (invalid_excluded a [8,7,0,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,0,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,0,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,0,6,8] (by decide +kernel)))

theorem node_2696 : Excluded a [8,7,0] :=
  branch_excluded a [8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,0,0] (by decide +kernel))
      node_2697
      node_2698
      (invalid_excluded a [8,7,0,3] (by decide +kernel))
      (invalid_excluded a [8,7,0,4] (by decide +kernel))
      node_2715
      node_2716
      (invalid_excluded a [8,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,0,8] (by decide +kernel)))

theorem node_2729 : Excluded a [8,7,1,0,2,3] :=
  predecessor_excluded a [8,7,1,0,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_2733 : Excluded a [8,7,1,0,2,4,3,5,6] :=
  predecessor_excluded a [8,7,1,0,2,4,3,5,6] 0 6 7 8 (by decide) (by decide +kernel)

theorem node_2732 : Excluded a [8,7,1,0,2,4,3,5] :=
  branch_excluded a [8,7,1,0,2,4,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,0,2,4,3,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,5,2] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,5,3] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,5,4] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,5,5] (by decide +kernel))
      node_2733
      (invalid_excluded a [8,7,1,0,2,4,3,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,5,8] (by decide +kernel)))

def b_2735 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 4
  | 6 => 3
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_2735 : LosingRegion (edgeOf a b_2735) 0 :=
  losingMask a b_2735 0 1210107572054781745792000
    (by decide +kernel) (by decide +kernel)

theorem node_2735 : Excluded a [8,7,1,0,2,4,3,6,5] :=
  losing_excluded a [8,7,1,0,2,4,3,6,5] (by decide) b_2735 (by decide +kernel) 1 0 6 cert_2735 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2735 1 0 ∧ 6 ≠ 1 ∧ maskRegion 1210107572054781745792000 1 6; decide +kernel)

theorem node_2734 : Excluded a [8,7,1,0,2,4,3,6] :=
  branch_excluded a [8,7,1,0,2,4,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,0,2,4,3,6,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,6,1] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,6,2] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,6,4] (by decide +kernel))
      node_2735
      (invalid_excluded a [8,7,1,0,2,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,6,8] (by decide +kernel)))

theorem node_2731 : Excluded a [8,7,1,0,2,4,3] :=
  branch_excluded a [8,7,1,0,2,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,0,2,4,3,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,1] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,3] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,4] (by decide +kernel))
      node_2732
      node_2734
      (invalid_excluded a [8,7,1,0,2,4,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,3,8] (by decide +kernel)))

theorem node_2736 : Excluded a [8,7,1,0,2,4,5] :=
  predecessor_excluded a [8,7,1,0,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2730 : Excluded a [8,7,1,0,2,4] :=
  branch_excluded a [8,7,1,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,0,2,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,2] (by decide +kernel))
      node_2731
      (invalid_excluded a [8,7,1,0,2,4,4] (by decide +kernel))
      node_2736
      (invalid_excluded a [8,7,1,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,4,8] (by decide +kernel)))

theorem node_2728 : Excluded a [8,7,1,0,2] :=
  branch_excluded a [8,7,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,2] (by decide +kernel))
      node_2729
      node_2730
      (invalid_excluded a [8,7,1,0,2,5] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,2,8] (by decide +kernel)))

theorem node_2740 : Excluded a [8,7,1,0,3,2,4,5] :=
  predecessor_excluded a [8,7,1,0,3,2,4,5] 0 5 6 7 (by decide) (by decide +kernel)

def b_2742 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
  | 6 => 4
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_2742 : LosingRegion (edgeOf a b_2742) 0 :=
  losingMask a b_2742 0 1210116972108029252113408
    (by decide +kernel) (by decide +kernel)

theorem node_2742 : Excluded a [8,7,1,0,3,2,4,6,5] :=
  losing_excluded a [8,7,1,0,3,2,4,6,5] (by decide) b_2742 (by decide +kernel) 1 0 3 cert_2742 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2742 1 0 ∧ 3 ≠ 1 ∧ maskRegion 1210116972108029252113408 1 3; decide +kernel)

theorem node_2741 : Excluded a [8,7,1,0,3,2,4,6] :=
  branch_excluded a [8,7,1,0,3,2,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,0,3,2,4,6,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,4,6,1] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,4,6,4] (by decide +kernel))
      node_2742
      (invalid_excluded a [8,7,1,0,3,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,4,6,8] (by decide +kernel)))

theorem node_2739 : Excluded a [8,7,1,0,3,2,4] :=
  branch_excluded a [8,7,1,0,3,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,0,3,2,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,4,2] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,4,3] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,4,4] (by decide +kernel))
      node_2740
      node_2741
      (invalid_excluded a [8,7,1,0,3,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,4,8] (by decide +kernel)))

def b_2745 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
  | 6 => 5
  | 7 => 4
  | 8 => 6
  | _ => 0

def cert_2745 : LosingRegion (edgeOf a b_2745) 0 :=
  losingMask a b_2745 0 1210107601524029815522304
    (by decide +kernel) (by decide +kernel)

theorem node_2745 : Excluded a [8,7,1,0,3,2,5,4,6] :=
  losing_excluded a [8,7,1,0,3,2,5,4,6] (by decide) b_2745 (by decide +kernel) 4 0 2 cert_2745 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_2745 4 0 ∧ 2 ≠ 4 ∧ maskRegion 1210107601524029815522304 4 2; decide +kernel)

theorem node_2744 : Excluded a [8,7,1,0,3,2,5,4] :=
  branch_excluded a [8,7,1,0,3,2,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,0,3,2,5,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,5,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,5,4,2] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,5,4,3] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,5,4,5] (by decide +kernel))
      node_2745
      (invalid_excluded a [8,7,1,0,3,2,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,5,4,8] (by decide +kernel)))

theorem node_2746 : Excluded a [8,7,1,0,3,2,5,6] :=
  predecessor_excluded a [8,7,1,0,3,2,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_2743 : Excluded a [8,7,1,0,3,2,5] :=
  branch_excluded a [8,7,1,0,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,0,3,2,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,5,3] (by decide +kernel))
      node_2744
      (invalid_excluded a [8,7,1,0,3,2,5,5] (by decide +kernel))
      node_2746
      (invalid_excluded a [8,7,1,0,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,5,8] (by decide +kernel)))

theorem node_2738 : Excluded a [8,7,1,0,3,2] :=
  branch_excluded a [8,7,1,0,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,0,3,2,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,1] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,3] (by decide +kernel))
      node_2739
      node_2743
      (invalid_excluded a [8,7,1,0,3,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,2,8] (by decide +kernel)))

theorem node_2747 : Excluded a [8,7,1,0,3,4] :=
  predecessor_excluded a [8,7,1,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2737 : Excluded a [8,7,1,0,3] :=
  branch_excluded a [8,7,1,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,0,3,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,1] (by decide +kernel))
      node_2738
      (invalid_excluded a [8,7,1,0,3,3] (by decide +kernel))
      node_2747
      (invalid_excluded a [8,7,1,0,3,5] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,3,8] (by decide +kernel)))

theorem node_2748 : Excluded a [8,7,1,0,6] :=
  source_excluded a [8,7,1,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2727 : Excluded a [8,7,1,0] :=
  branch_excluded a [8,7,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,1] (by decide +kernel))
      node_2728
      node_2737
      (invalid_excluded a [8,7,1,0,4] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,5] (by decide +kernel))
      node_2748
      (invalid_excluded a [8,7,1,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,0,8] (by decide +kernel)))

theorem node_2749 : Excluded a [8,7,1,2] :=
  predecessor_excluded a [8,7,1,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_2750 : Excluded a [8,7,1,5] :=
  source_excluded a [8,7,1,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2754 : Excluded a [8,7,1,6,0,2,3] :=
  predecessor_excluded a [8,7,1,6,0,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_2755 : Excluded a [8,7,1,6,0,2,4] :=
  source_excluded a [8,7,1,6,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2756 : Excluded a [8,7,1,6,0,2,5] :=
  predecessor_excluded a [8,7,1,6,0,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2753 : Excluded a [8,7,1,6,0,2] :=
  branch_excluded a [8,7,1,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,6,0,2,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,0,2,1] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,0,2,2] (by decide +kernel))
      node_2754
      node_2755
      node_2756
      (invalid_excluded a [8,7,1,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,0,2,8] (by decide +kernel)))

theorem node_2757 : Excluded a [8,7,1,6,0,3] :=
  source_excluded a [8,7,1,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2758 : Excluded a [8,7,1,6,0,4] :=
  source_excluded a [8,7,1,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2752 : Excluded a [8,7,1,6,0] :=
  branch_excluded a [8,7,1,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,6,0,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,0,1] (by decide +kernel))
      node_2753
      node_2757
      node_2758
      (invalid_excluded a [8,7,1,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,0,8] (by decide +kernel)))

theorem node_2762 : Excluded a [8,7,1,6,2,0,3,4] :=
  predecessor_excluded a [8,7,1,6,2,0,3,4] 0 4 6 7 (by decide) (by decide +kernel)

theorem node_2763 : Excluded a [8,7,1,6,2,0,3,5] :=
  predecessor_excluded a [8,7,1,6,2,0,3,5] 1 0 7 5 (by decide) (by decide +kernel)

theorem node_2761 : Excluded a [8,7,1,6,2,0,3] :=
  branch_excluded a [8,7,1,6,2,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,6,2,0,3,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,2,0,3,1] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,2,0,3,2] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,2,0,3,3] (by decide +kernel))
      node_2762
      node_2763
      (invalid_excluded a [8,7,1,6,2,0,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,2,0,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,2,0,3,8] (by decide +kernel)))

theorem node_2764 : Excluded a [8,7,1,6,2,0,4] :=
  source_excluded a [8,7,1,6,2,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2765 : Excluded a [8,7,1,6,2,0,5] :=
  predecessor_excluded a [8,7,1,6,2,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2760 : Excluded a [8,7,1,6,2,0] :=
  branch_excluded a [8,7,1,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,1,6,2,0,0] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,2,0,1] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,2,0,2] (by decide +kernel))
      node_2761
      node_2764
      node_2765
      (invalid_excluded a [8,7,1,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,2,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,2,0,8] (by decide +kernel)))

theorem node_2766 : Excluded a [8,7,1,6,2,3] :=
  source_excluded a [8,7,1,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2767 : Excluded a [8,7,1,6,2,4] :=
  source_excluded a [8,7,1,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2759 : Excluded a [8,7,1,6,2] :=
  branch_excluded a [8,7,1,6,2] (by decide)
    (fin9_cases _
      node_2760
      (invalid_excluded a [8,7,1,6,2,1] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,2,2] (by decide +kernel))
      node_2766
      node_2767
      (invalid_excluded a [8,7,1,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,2,8] (by decide +kernel)))

theorem node_2768 : Excluded a [8,7,1,6,3] :=
  predecessor_excluded a [8,7,1,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2751 : Excluded a [8,7,1,6] :=
  branch_excluded a [8,7,1,6] (by decide)
    (fin9_cases _
      node_2752
      (invalid_excluded a [8,7,1,6,1] (by decide +kernel))
      node_2759
      node_2768
      (invalid_excluded a [8,7,1,6,4] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,6,8] (by decide +kernel)))

theorem node_2726 : Excluded a [8,7,1] :=
  branch_excluded a [8,7,1] (by decide)
    (fin9_cases _
      node_2727
      (invalid_excluded a [8,7,1,1] (by decide +kernel))
      node_2749
      (invalid_excluded a [8,7,1,3] (by decide +kernel))
      (invalid_excluded a [8,7,1,4] (by decide +kernel))
      node_2750
      node_2751
      (invalid_excluded a [8,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,1,8] (by decide +kernel)))

theorem node_2769 : Excluded a [8,7,4] :=
  source_excluded a [8,7,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2772 : Excluded a [8,7,5,0,1] :=
  predecessor_excluded a [8,7,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2773 : Excluded a [8,7,5,0,2] :=
  source_excluded a [8,7,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2774 : Excluded a [8,7,5,0,3] :=
  source_excluded a [8,7,5,0,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2775 : Excluded a [8,7,5,0,6] :=
  source_excluded a [8,7,5,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2771 : Excluded a [8,7,5,0] :=
  branch_excluded a [8,7,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,5,0,0] (by decide +kernel))
      node_2772
      node_2773
      node_2774
      (invalid_excluded a [8,7,5,0,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,5] (by decide +kernel))
      node_2775
      (invalid_excluded a [8,7,5,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,0,8] (by decide +kernel)))

theorem node_2779 : Excluded a [8,7,5,1,0,2,3] :=
  predecessor_excluded a [8,7,5,1,0,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_2781 : Excluded a [8,7,5,1,0,2,4,3] :=
  predecessor_excluded a [8,7,5,1,0,2,4,3] 0 3 1 7 (by decide) (by decide +kernel)

theorem node_2783 : Excluded a [8,7,5,1,0,2,4,6,3] :=
  predecessor_excluded a [8,7,5,1,0,2,4,6,3] 2 1 8 3 (by decide) (by decide +kernel)

theorem node_2782 : Excluded a [8,7,5,1,0,2,4,6] :=
  branch_excluded a [8,7,5,1,0,2,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,5,1,0,2,4,6,0] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,4,6,1] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,4,6,2] (by decide +kernel))
      node_2783
      (invalid_excluded a [8,7,5,1,0,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,4,6,8] (by decide +kernel)))

theorem node_2780 : Excluded a [8,7,5,1,0,2,4] :=
  branch_excluded a [8,7,5,1,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,5,1,0,2,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,4,2] (by decide +kernel))
      node_2781
      (invalid_excluded a [8,7,5,1,0,2,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,4,5] (by decide +kernel))
      node_2782
      (invalid_excluded a [8,7,5,1,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,4,8] (by decide +kernel)))

theorem node_2778 : Excluded a [8,7,5,1,0,2] :=
  branch_excluded a [8,7,5,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,5,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,2] (by decide +kernel))
      node_2779
      node_2780
      (invalid_excluded a [8,7,5,1,0,2,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,2,8] (by decide +kernel)))

theorem node_2784 : Excluded a [8,7,5,1,0,3] :=
  source_excluded a [8,7,5,1,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2785 : Excluded a [8,7,5,1,0,4] :=
  predecessor_excluded a [8,7,5,1,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2777 : Excluded a [8,7,5,1,0] :=
  branch_excluded a [8,7,5,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,5,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,1] (by decide +kernel))
      node_2778
      node_2784
      node_2785
      (invalid_excluded a [8,7,5,1,0,5] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,0,8] (by decide +kernel)))

theorem node_2786 : Excluded a [8,7,5,1,2] :=
  source_excluded a [8,7,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2787 : Excluded a [8,7,5,1,3] :=
  source_excluded a [8,7,5,1,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2788 : Excluded a [8,7,5,1,6] :=
  source_excluded a [8,7,5,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2776 : Excluded a [8,7,5,1] :=
  branch_excluded a [8,7,5,1] (by decide)
    (fin9_cases _
      node_2777
      (invalid_excluded a [8,7,5,1,1] (by decide +kernel))
      node_2786
      node_2787
      (invalid_excluded a [8,7,5,1,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,5] (by decide +kernel))
      node_2788
      (invalid_excluded a [8,7,5,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,1,8] (by decide +kernel)))

theorem node_2789 : Excluded a [8,7,5,2] :=
  predecessor_excluded a [8,7,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_2790 : Excluded a [8,7,5,6] :=
  predecessor_excluded a [8,7,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_2770 : Excluded a [8,7,5] :=
  branch_excluded a [8,7,5] (by decide)
    (fin9_cases _
      node_2771
      node_2776
      node_2789
      (invalid_excluded a [8,7,5,3] (by decide +kernel))
      (invalid_excluded a [8,7,5,4] (by decide +kernel))
      (invalid_excluded a [8,7,5,5] (by decide +kernel))
      node_2790
      (invalid_excluded a [8,7,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,5,8] (by decide +kernel)))

theorem node_2793 : Excluded a [8,7,6,0,1] :=
  predecessor_excluded a [8,7,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2794 : Excluded a [8,7,6,0,2] :=
  predecessor_excluded a [8,7,6,0,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_2796 : Excluded a [8,7,6,0,3,1] :=
  predecessor_excluded a [8,7,6,0,3,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_2797 : Excluded a [8,7,6,0,3,2] :=
  source_excluded a [8,7,6,0,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2798 : Excluded a [8,7,6,0,3,4] :=
  predecessor_excluded a [8,7,6,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2795 : Excluded a [8,7,6,0,3] :=
  branch_excluded a [8,7,6,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,0,3,0] (by decide +kernel))
      node_2796
      node_2797
      (invalid_excluded a [8,7,6,0,3,3] (by decide +kernel))
      node_2798
      (invalid_excluded a [8,7,6,0,3,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,3,8] (by decide +kernel)))

theorem node_2792 : Excluded a [8,7,6,0] :=
  branch_excluded a [8,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,0,0] (by decide +kernel))
      node_2793
      node_2794
      node_2795
      (invalid_excluded a [8,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,0,8] (by decide +kernel)))

theorem node_2801 : Excluded a [8,7,6,1,0,2] :=
  source_excluded a [8,7,6,1,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2802 : Excluded a [8,7,6,1,0,3] :=
  source_excluded a [8,7,6,1,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2804 : Excluded a [8,7,6,1,0,4,2] :=
  source_excluded a [8,7,6,1,0,4,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2805 : Excluded a [8,7,6,1,0,4,3] :=
  source_excluded a [8,7,6,1,0,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2806 : Excluded a [8,7,6,1,0,4,5] :=
  predecessor_excluded a [8,7,6,1,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2803 : Excluded a [8,7,6,1,0,4] :=
  branch_excluded a [8,7,6,1,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,1] (by decide +kernel))
      node_2804
      node_2805
      (invalid_excluded a [8,7,6,1,0,4,4] (by decide +kernel))
      node_2806
      (invalid_excluded a [8,7,6,1,0,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,4,8] (by decide +kernel)))

theorem node_2800 : Excluded a [8,7,6,1,0] :=
  branch_excluded a [8,7,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,1] (by decide +kernel))
      node_2801
      node_2802
      node_2803
      (invalid_excluded a [8,7,6,1,0,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,0,8] (by decide +kernel)))

theorem node_2807 : Excluded a [8,7,6,1,2] :=
  predecessor_excluded a [8,7,6,1,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_2810 : Excluded a [8,7,6,1,3,0,2] :=
  source_excluded a [8,7,6,1,3,0,2] 1 0 6 (by decide) (by decide +kernel)

theorem node_2811 : Excluded a [8,7,6,1,3,0,4] :=
  predecessor_excluded a [8,7,6,1,3,0,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_2813 : Excluded a [8,7,6,1,3,0,5,2] :=
  source_excluded a [8,7,6,1,3,0,5,2] 1 0 7 (by decide) (by decide +kernel)

theorem node_2815 : Excluded a [8,7,6,1,3,0,5,4,2] :=
  predecessor_excluded a [8,7,6,1,3,0,5,4,2] 3 2 0 8 (by decide) (by decide +kernel)

theorem node_2814 : Excluded a [8,7,6,1,3,0,5,4] :=
  branch_excluded a [8,7,6,1,3,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,3,0,5,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,0,5,4,1] (by decide +kernel))
      node_2815
      (invalid_excluded a [8,7,6,1,3,0,5,4,3] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,0,5,4,8] (by decide +kernel)))

theorem node_2812 : Excluded a [8,7,6,1,3,0,5] :=
  branch_excluded a [8,7,6,1,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,3,0,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,0,5,1] (by decide +kernel))
      node_2813
      (invalid_excluded a [8,7,6,1,3,0,5,3] (by decide +kernel))
      node_2814
      (invalid_excluded a [8,7,6,1,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,0,5,8] (by decide +kernel)))

theorem node_2809 : Excluded a [8,7,6,1,3,0] :=
  branch_excluded a [8,7,6,1,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,1,3,0,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,0,1] (by decide +kernel))
      node_2810
      (invalid_excluded a [8,7,6,1,3,0,3] (by decide +kernel))
      node_2811
      node_2812
      (invalid_excluded a [8,7,6,1,3,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,0,8] (by decide +kernel)))

theorem node_2816 : Excluded a [8,7,6,1,3,2] :=
  source_excluded a [8,7,6,1,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2817 : Excluded a [8,7,6,1,3,4] :=
  predecessor_excluded a [8,7,6,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2808 : Excluded a [8,7,6,1,3] :=
  branch_excluded a [8,7,6,1,3] (by decide)
    (fin9_cases _
      node_2809
      (invalid_excluded a [8,7,6,1,3,1] (by decide +kernel))
      node_2816
      (invalid_excluded a [8,7,6,1,3,3] (by decide +kernel))
      node_2817
      (invalid_excluded a [8,7,6,1,3,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,3,8] (by decide +kernel)))

theorem node_2799 : Excluded a [8,7,6,1] :=
  branch_excluded a [8,7,6,1] (by decide)
    (fin9_cases _
      node_2800
      (invalid_excluded a [8,7,6,1,1] (by decide +kernel))
      node_2807
      node_2808
      (invalid_excluded a [8,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,1,8] (by decide +kernel)))

theorem node_2820 : Excluded a [8,7,6,2,0,1] :=
  predecessor_excluded a [8,7,6,2,0,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_2821 : Excluded a [8,7,6,2,0,3] :=
  source_excluded a [8,7,6,2,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2823 : Excluded a [8,7,6,2,0,4,1] :=
  source_excluded a [8,7,6,2,0,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_2824 : Excluded a [8,7,6,2,0,4,3] :=
  source_excluded a [8,7,6,2,0,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2825 : Excluded a [8,7,6,2,0,4,5] :=
  predecessor_excluded a [8,7,6,2,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2822 : Excluded a [8,7,6,2,0,4] :=
  branch_excluded a [8,7,6,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,2,0,4,0] (by decide +kernel))
      node_2823
      (invalid_excluded a [8,7,6,2,0,4,2] (by decide +kernel))
      node_2824
      (invalid_excluded a [8,7,6,2,0,4,4] (by decide +kernel))
      node_2825
      (invalid_excluded a [8,7,6,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,0,4,8] (by decide +kernel)))

theorem node_2819 : Excluded a [8,7,6,2,0] :=
  branch_excluded a [8,7,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,2,0,0] (by decide +kernel))
      node_2820
      (invalid_excluded a [8,7,6,2,0,2] (by decide +kernel))
      node_2821
      node_2822
      (invalid_excluded a [8,7,6,2,0,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,0,8] (by decide +kernel)))

theorem node_2828 : Excluded a [8,7,6,2,1,0,3] :=
  source_excluded a [8,7,6,2,1,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2829 : Excluded a [8,7,6,2,1,0,4] :=
  predecessor_excluded a [8,7,6,2,1,0,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_2831 : Excluded a [8,7,6,2,1,0,5,3] :=
  predecessor_excluded a [8,7,6,2,1,0,5,3] 0 3 1 7 (by decide) (by decide +kernel)

def b_2833 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 7
  | 2 => 6
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 5
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_2833 : LosingRegion (edgeOf a b_2833) 0 :=
  losingMask a b_2833 0 1210107565290464350340096
    (by decide +kernel) (by decide +kernel)

theorem node_2833 : Excluded a [8,7,6,2,1,0,5,4,3] :=
  losing_excluded a [8,7,6,2,1,0,5,4,3] (by decide) b_2833 (by decide +kernel) 1 0 6 cert_2833 (by change 1 ≠ 0 ∧ ¬ edgeOf a b_2833 1 0 ∧ 6 ≠ 1 ∧ maskRegion 1210107565290464350340096 1 6; decide +kernel)

theorem node_2832 : Excluded a [8,7,6,2,1,0,5,4] :=
  branch_excluded a [8,7,6,2,1,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,2,1,0,5,4,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,4,2] (by decide +kernel))
      node_2833
      (invalid_excluded a [8,7,6,2,1,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,4,8] (by decide +kernel)))

theorem node_2830 : Excluded a [8,7,6,2,1,0,5] :=
  branch_excluded a [8,7,6,2,1,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,2,1,0,5,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,2] (by decide +kernel))
      node_2831
      node_2832
      (invalid_excluded a [8,7,6,2,1,0,5,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,5,8] (by decide +kernel)))

theorem node_2827 : Excluded a [8,7,6,2,1,0] :=
  branch_excluded a [8,7,6,2,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,7,6,2,1,0,0] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,2] (by decide +kernel))
      node_2828
      node_2829
      node_2830
      (invalid_excluded a [8,7,6,2,1,0,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,0,8] (by decide +kernel)))

theorem node_2834 : Excluded a [8,7,6,2,1,3] :=
  source_excluded a [8,7,6,2,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2836 : Excluded a [8,7,6,2,1,4,0] :=
  predecessor_excluded a [8,7,6,2,1,4,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2837 : Excluded a [8,7,6,2,1,4,3] :=
  source_excluded a [8,7,6,2,1,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2838 : Excluded a [8,7,6,2,1,4,5] :=
  predecessor_excluded a [8,7,6,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2835 : Excluded a [8,7,6,2,1,4] :=
  branch_excluded a [8,7,6,2,1,4] (by decide)
    (fin9_cases _
      node_2836
      (invalid_excluded a [8,7,6,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,2] (by decide +kernel))
      node_2837
      (invalid_excluded a [8,7,6,2,1,4,4] (by decide +kernel))
      node_2838
      (invalid_excluded a [8,7,6,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,4,8] (by decide +kernel)))

theorem node_2826 : Excluded a [8,7,6,2,1] :=
  branch_excluded a [8,7,6,2,1] (by decide)
    (fin9_cases _
      node_2827
      (invalid_excluded a [8,7,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,2] (by decide +kernel))
      node_2834
      node_2835
      (invalid_excluded a [8,7,6,2,1,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,1,8] (by decide +kernel)))

theorem node_2839 : Excluded a [8,7,6,2,3] :=
  predecessor_excluded a [8,7,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2818 : Excluded a [8,7,6,2] :=
  branch_excluded a [8,7,6,2] (by decide)
    (fin9_cases _
      node_2819
      node_2826
      (invalid_excluded a [8,7,6,2,2] (by decide +kernel))
      node_2839
      (invalid_excluded a [8,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,2,8] (by decide +kernel)))

theorem node_2840 : Excluded a [8,7,6,5] :=
  source_excluded a [8,7,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2791 : Excluded a [8,7,6] :=
  branch_excluded a [8,7,6] (by decide)
    (fin9_cases _
      node_2792
      node_2799
      node_2818
      (invalid_excluded a [8,7,6,3] (by decide +kernel))
      (invalid_excluded a [8,7,6,4] (by decide +kernel))
      node_2840
      (invalid_excluded a [8,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,7,6,8] (by decide +kernel)))

theorem node_2695 : Excluded a [8,7] :=
  branch_excluded a [8,7] (by decide)
    (fin9_cases _
      node_2696
      node_2726
      (invalid_excluded a [8,7,2] (by decide +kernel))
      (invalid_excluded a [8,7,3] (by decide +kernel))
      node_2769
      node_2770
      node_2791
      (invalid_excluded a [8,7,7] (by decide +kernel))
      (invalid_excluded a [8,7,8] (by decide +kernel)))

theorem node_2395 : Excluded a [8] :=
  branch_excluded a [8] (by decide)
    (fin9_cases _
      node_2396
      (invalid_excluded a [8,1] (by decide +kernel))
      (invalid_excluded a [8,2] (by decide +kernel))
      node_2397
      node_2398
      node_2459
      node_2572
      node_2695
      (invalid_excluded a [8,8] (by decide +kernel)))

theorem node_1 : Excluded a [] :=
  branch_excluded a [] (by decide)
    (fin9_cases _
      (invalid_excluded a [0] (by decide +kernel))
      (invalid_excluded a [1] (by decide +kernel))
      node_2
      node_3
      node_321
      node_797
      node_1324
      node_1873
      node_2395)

theorem every_second_factor_blocked (b : Assignment 9) (valid : Valid a b) : Blocked a b :=
  node_1 b valid (by intro i h; simp at h)

theorem primary_loopless : ∀ i : Fin 9, a i ≠ i := by decide +kernel

#print axioms every_second_factor_blocked
end Delivery.FiniteExclusion.Cycle9
