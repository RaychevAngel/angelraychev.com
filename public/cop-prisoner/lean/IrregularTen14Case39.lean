import IrregularTen14Base

namespace Delivery.IrregularTen14.Case39
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 240 192 240 224 0 0 0 0 0 0), upper := (rows 259 50 13 28 752 736 736 736 992 736), lower := (rows 259 50 13 28 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [258,48,9,20] 13 :=
  bound_sound D R [258,48,9,20] 13 bound_2
    ((Boolean.boundCheck_true D R [258,48,9,20] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 240 192 240 192 0 0 0 0 0 0), upper := (rows 259 50 13 56 724 740 708 708 964 708), lower := (rows 259 50 13 56 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [258,48,9,48] 13 :=
  bound_sound D R [258,48,9,48] 13 bound_3
    ((Boolean.boundCheck_true D R [258,48,9,48] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 240 192 240 176 0 0 0 0 0 0), upper := (rows 259 50 13 76 752 752 752 752 1008 752), lower := (rows 259 50 13 76 16 32 64 128 256 512), losses := [] }

theorem upper_4 : Upper D R [258,48,9,68] 13 :=
  bound_sound D R [258,48,9,68] 13 bound_4
    ((Boolean.boundCheck_true D R [258,48,9,68] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 240 192 240 160 0 0 0 0 0 0), upper := (rows 259 50 13 88 756 740 740 740 996 740), lower := (rows 259 50 13 88 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [258,48,9,80] 13 :=
  bound_sound D R [258,48,9,80] 13 bound_5
    ((Boolean.boundCheck_true D R [258,48,9,80] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 240 192 240 48 0 0 0 0 0 0), upper := (rows 259 50 13 200 756 756 756 756 1012 756), lower := (rows 259 50 13 200 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [258,48,9,192] 13 :=
  bound_sound D R [258,48,9,192] 13 bound_6
    ((Boolean.boundCheck_true D R [258,48,9,192] 13 bound_6).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 208 192 208 208 0 0 0 0 0 0), upper := (rows 259 50 13 524 48 240 208 208 464 720), lower := (rows 259 50 13 524 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 3 2 7 11 16 0 82 146 274 530), good := (rows 975 991 13 524 976 0 64 128 256 512) }] }

theorem upper_8 : Upper D R [258,48,9,516,32] 13 :=
  bound_sound D R [258,48,9,516,32] 13 bound_8
    ((Boolean.boundCheck_true D R [258,48,9,516,32] 13 bound_8).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 259 50 13 524 80 48 224 224 480 736), lower := (rows 259 50 13 524 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 7 11 0 32 98 162 290 546), good := (rows 975 1007 13 524 64 992 64 128 256 512) }] }

theorem upper_10 : Upper D R [258,48,9,516,64,16] 13 :=
  bound_sound D R [258,48,9,516,64,16] 13 bound_10
    ((Boolean.boundCheck_true D R [258,48,9,516,64,16] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 176 192 176 176 0 0 0 0 0 0), upper := (rows 259 50 13 524 80 96 240 176 432 688), lower := (rows 259 50 13 524 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 3 2 7 11 16 32 0 130 258 514), good := (rows 911 959 13 524 16 32 0 128 256 512) }] }

theorem upper_11 : Upper D R [258,48,9,516,64,64] 13 :=
  bound_sound D R [258,48,9,516,64,64] 13 bound_11
    ((Boolean.boundCheck_true D R [258,48,9,516,64,64] 13 bound_11).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 259 50 13 524 80 160 80 224 480 736), lower := (rows 259 50 13 524 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 7 10 0 242 64 208 336 592), good := (rows 303 943 13 524 992 160 992 160 256 512) }] }

theorem upper_13 : Upper D R [258,48,9,516,64,128,16] 13 :=
  bound_sound D R [258,48,9,516,64,128,16] 13 bound_13
    ((Boolean.boundCheck_true D R [258,48,9,516,64,128,16] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 208 192 208 208 0 0 0 0 0 0), upper := (rows 259 50 13 524 80 160 96 208 464 720), lower := (rows 259 50 13 524 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 3 2 7 10 80 0 64 208 336 592), good := (rows 271 927 13 524 976 128 976 128 256 512) }] }

theorem upper_14 : Upper D R [258,48,9,516,64,128,32] 13 :=
  bound_sound D R [258,48,9,516,64,128,32] 13 bound_14
    ((Boolean.boundCheck_true D R [258,48,9,516,64,128,32] 13 bound_14).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 240 128 240 240 0 0 0 0 0 0), upper := (rows 259 50 13 524 80 160 192 240 368 624), lower := (rows 259 50 13 524 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 1 18 4 8 16 224 0 128 256 512), good := (rows 259 50 13 524 50 160 160 160 256 512) }] }

theorem upper_15 : Upper D R [258,48,9,516,64,128,128] 13 :=
  bound_sound D R [258,48,9,516,64,128,128] 13 bound_15
    ((Boolean.boundCheck_true D R [258,48,9,516,64,128,128] 13 bound_15).mp (by decide +kernel))

def route_12 : Route 10 := (fun mask => (mask,id))

theorem upper_12 : Upper D R [258,48,9,516,64,128] 13 := by
  apply routed_branch D R [258,48,9,516,64,128] 13 (by decide) (choices 1) [16,32,128] route_12
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,48,9,516,64,128] (choices 1) [16,32,128] route_12).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_13
  · exact upper_14
  · exact upper_15

def route_9 : Route 10 := (fun mask => (mask,id))

theorem upper_9 : Upper D R [258,48,9,516,64] 13 := by
  apply routed_branch D R [258,48,9,516,64] 13 (by decide) (choices 1) [16,64,128] route_9
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,48,9,516,64] (choices 1) [16,64,128] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_10
  · exact upper_11
  · exact upper_12

def route_7 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_7 : Upper D R [258,48,9,516] 13 := by
  apply routed_branch D R [258,48,9,516] 13 (by decide) (choices 1) [32,64] route_7
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,48,9,516] (choices 1) [32,64] route_7).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_8
  · exact upper_9

def bound_16 : Bound 10 := { allowed := (rows 240 192 240 224 0 0 0 0 0 0), upper := (rows 259 50 13 536 244 228 228 228 484 740), lower := (rows 259 50 13 536 16 32 64 128 256 512), losses := [] }

theorem upper_16 : Upper D R [258,48,9,528] 13 :=
  bound_sound D R [258,48,9,528] 13 bound_16
    ((Boolean.boundCheck_true D R [258,48,9,528] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 240 192 240 176 0 0 0 0 0 0), upper := (rows 259 50 13 584 244 244 244 244 500 756), lower := (rows 259 50 13 584 16 32 64 128 256 512), losses := [] }

theorem upper_17 : Upper D R [258,48,9,576] 13 :=
  bound_sound D R [258,48,9,576] 13 bound_17
    ((Boolean.boundCheck_true D R [258,48,9,576] 13 bound_17).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [258,48,9] 13 := by
  apply routed_branch D R [258,48,9] 13 (by decide) (choices 2) [20,48,68,80,192,516,528,576] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,48,9] (choices 2) [20,48,68,80,192,516,528,576] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5
  · exact upper_6
  · exact upper_7
  · exact upper_16
  · exact upper_17

def bound_18 : Bound 10 := { allowed := (rows 240 192 224 240 0 0 0 0 0 0), upper := (rows 259 50 21 748 764 748 748 748 1004 748), lower := (rows 259 50 21 8 16 32 64 128 256 512), losses := [] }

theorem upper_18 : Upper D R [258,48,17] 13 :=
  bound_sound D R [258,48,17] 13 bound_18
    ((Boolean.boundCheck_true D R [258,48,17] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 240 192 224 240 0 0 0 0 0 0), upper := (rows 259 50 28 749 757 741 741 741 997 741), lower := (rows 259 50 28 8 16 32 64 128 256 512), losses := [] }

theorem upper_19 : Upper D R [258,48,24] 13 :=
  bound_sound D R [258,48,24] 13 bound_19
    ((Boolean.boundCheck_true D R [258,48,24] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 240 192 192 240 0 0 0 0 0 0), upper := (rows 259 50 52 717 733 749 717 717 973 717), lower := (rows 259 50 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_20 : Upper D R [258,48,48] 13 :=
  bound_sound D R [258,48,48] 13 bound_20
    ((Boolean.boundCheck_true D R [258,48,48] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 240 192 176 240 0 0 0 0 0 0), upper := (rows 259 50 69 764 764 764 764 764 1020 764), lower := (rows 259 50 69 8 16 32 64 128 256 512), losses := [] }

theorem upper_21 : Upper D R [258,48,65] 13 :=
  bound_sound D R [258,48,65] 13 bound_21
    ((Boolean.boundCheck_true D R [258,48,65] 13 bound_21).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 240 192 176 240 0 0 0 0 0 0), upper := (rows 259 50 76 765 757 757 757 757 1013 757), lower := (rows 259 50 76 8 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [258,48,72] 13 :=
  bound_sound D R [258,48,72] 13 bound_22
    ((Boolean.boundCheck_true D R [258,48,72] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 240 192 160 240 0 0 0 0 0 0), upper := (rows 259 50 84 749 765 749 749 749 1005 749), lower := (rows 259 50 84 8 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [258,48,80] 13 :=
  bound_sound D R [258,48,80] 13 bound_23
    ((Boolean.boundCheck_true D R [258,48,80] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 240 192 48 240 0 0 0 0 0 0), upper := (rows 259 50 196 765 765 765 765 765 1021 765), lower := (rows 259 50 196 8 16 32 64 128 256 512), losses := [] }

theorem upper_24 : Upper D R [258,48,192] 13 :=
  bound_sound D R [258,48,192] 13 bound_24
    ((Boolean.boundCheck_true D R [258,48,192] 13 bound_24).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 240 192 240 224 0 0 0 0 0 0), upper := (rows 259 50 517 28 248 232 232 232 488 744), lower := (rows 259 50 517 28 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [258,48,513,20] 13 :=
  bound_sound D R [258,48,513,20] 13 bound_26
    ((Boolean.boundCheck_true D R [258,48,513,20] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 240 192 240 192 0 0 0 0 0 0), upper := (rows 259 50 517 56 220 236 204 204 460 716), lower := (rows 259 50 517 56 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [258,48,513,48] 13 :=
  bound_sound D R [258,48,513,48] 13 bound_27
    ((Boolean.boundCheck_true D R [258,48,513,48] 13 bound_27).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 240 192 240 176 0 0 0 0 0 0), upper := (rows 259 50 517 76 248 248 248 248 504 760), lower := (rows 259 50 517 76 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [258,48,513,68] 13 :=
  bound_sound D R [258,48,513,68] 13 bound_28
    ((Boolean.boundCheck_true D R [258,48,513,68] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 240 192 240 160 0 0 0 0 0 0), upper := (rows 259 50 517 88 252 236 236 236 492 748), lower := (rows 259 50 517 88 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [258,48,513,80] 13 :=
  bound_sound D R [258,48,513,80] 13 bound_29
    ((Boolean.boundCheck_true D R [258,48,513,80] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 240 192 240 48 0 0 0 0 0 0), upper := (rows 259 50 517 200 252 252 252 252 508 764), lower := (rows 259 50 517 200 16 32 64 128 256 512), losses := [] }

theorem upper_30 : Upper D R [258,48,513,192] 13 :=
  bound_sound D R [258,48,513,192] 13 bound_30
    ((Boolean.boundCheck_true D R [258,48,513,192] 13 bound_30).mp (by decide +kernel))

def route_25 : Route 10 := (fun mask => match mask with | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_25 : Upper D R [258,48,513] 13 := by
  apply routed_branch D R [258,48,513] 13 (by decide) (choices 2) [20,48,68,80,192] route_25
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,48,513] (choices 2) [20,48,68,80,192] route_25).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact upper_26
  · exact upper_27
  · exact upper_28
  · exact upper_29
  · exact upper_30

def bound_33 : Bound 10 := { allowed := (rows 208 192 208 208 0 0 0 0 0 0), upper := (rows 259 50 524 13 48 240 208 208 464 720), lower := (rows 259 50 524 13 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 3 2 7 11 16 0 82 146 274 530), good := (rows 975 991 524 13 976 0 64 128 256 512) }] }

theorem upper_33 : Upper D R [258,48,520,5,32] 13 :=
  bound_sound D R [258,48,520,5,32] 13 bound_33
    ((Boolean.boundCheck_true D R [258,48,520,5,32] 13 bound_33).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 259 50 524 13 80 48 224 224 480 736), lower := (rows 259 50 524 13 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 7 11 0 32 98 162 290 546), good := (rows 975 1007 524 13 64 992 64 128 256 512) }] }

theorem upper_35 : Upper D R [258,48,520,5,64,16] 13 :=
  bound_sound D R [258,48,520,5,64,16] 13 bound_35
    ((Boolean.boundCheck_true D R [258,48,520,5,64,16] 13 bound_35).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 176 192 176 176 0 0 0 0 0 0), upper := (rows 259 50 524 13 80 96 240 176 432 688), lower := (rows 259 50 524 13 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 3 2 7 11 16 32 0 130 258 514), good := (rows 911 959 524 13 16 32 0 128 256 512) }] }

theorem upper_36 : Upper D R [258,48,520,5,64,64] 13 :=
  bound_sound D R [258,48,520,5,64,64] 13 bound_36
    ((Boolean.boundCheck_true D R [258,48,520,5,64,64] 13 bound_36).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 259 50 524 13 80 160 80 224 480 736), lower := (rows 259 50 524 13 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 6 11 0 242 64 208 336 592), good := (rows 303 943 524 13 992 160 992 160 256 512) }] }

theorem upper_38 : Upper D R [258,48,520,5,64,128,16] 13 :=
  bound_sound D R [258,48,520,5,64,128,16] 13 bound_38
    ((Boolean.boundCheck_true D R [258,48,520,5,64,128,16] 13 bound_38).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 208 192 208 208 0 0 0 0 0 0), upper := (rows 259 50 524 13 80 160 96 208 464 720), lower := (rows 259 50 524 13 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 3 2 6 11 80 0 64 208 336 592), good := (rows 271 927 524 13 976 128 976 128 256 512) }] }

theorem upper_39 : Upper D R [258,48,520,5,64,128,32] 13 :=
  bound_sound D R [258,48,520,5,64,128,32] 13 bound_39
    ((Boolean.boundCheck_true D R [258,48,520,5,64,128,32] 13 bound_39).mp (by decide +kernel))

def bound_40 : Bound 10 := { allowed := (rows 240 128 240 240 0 0 0 0 0 0), upper := (rows 259 50 524 13 80 160 192 240 368 624), lower := (rows 259 50 524 13 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 1 18 4 8 16 224 0 128 256 512), good := (rows 259 50 524 13 50 160 160 160 256 512) }] }

theorem upper_40 : Upper D R [258,48,520,5,64,128,128] 13 :=
  bound_sound D R [258,48,520,5,64,128,128] 13 bound_40
    ((Boolean.boundCheck_true D R [258,48,520,5,64,128,128] 13 bound_40).mp (by decide +kernel))

def route_37 : Route 10 := (fun mask => (mask,id))

theorem upper_37 : Upper D R [258,48,520,5,64,128] 13 := by
  apply routed_branch D R [258,48,520,5,64,128] 13 (by decide) (choices 1) [16,32,128] route_37
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,48,520,5,64,128] (choices 1) [16,32,128] route_37).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_38
  · exact upper_39
  · exact upper_40

def route_34 : Route 10 := (fun mask => (mask,id))

theorem upper_34 : Upper D R [258,48,520,5,64] 13 := by
  apply routed_branch D R [258,48,520,5,64] 13 (by decide) (choices 1) [16,64,128] route_34
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,48,520,5,64] (choices 1) [16,64,128] route_34).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_35
  · exact upper_36
  · exact upper_37

def route_32 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_32 : Upper D R [258,48,520,5] 13 := by
  apply routed_branch D R [258,48,520,5] 13 (by decide) (choices 1) [32,64] route_32
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,48,520,5] (choices 1) [32,64] route_32).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_33
  · exact upper_34

def bound_41 : Bound 10 := { allowed := (rows 240 192 240 224 0 0 0 0 0 0), upper := (rows 259 50 524 25 244 228 228 228 484 740), lower := (rows 259 50 524 25 16 32 64 128 256 512), losses := [] }

theorem upper_41 : Upper D R [258,48,520,17] 13 :=
  bound_sound D R [258,48,520,17] 13 bound_41
    ((Boolean.boundCheck_true D R [258,48,520,17] 13 bound_41).mp (by decide +kernel))

def bound_42 : Bound 10 := { allowed := (rows 240 192 240 224 0 0 0 0 0 0), upper := (rows 259 50 524 28 241 225 225 225 481 737), lower := (rows 259 50 524 28 16 32 64 128 256 512), losses := [] }

theorem upper_42 : Upper D R [258,48,520,20] 13 :=
  bound_sound D R [258,48,520,20] 13 bound_42
    ((Boolean.boundCheck_true D R [258,48,520,20] 13 bound_42).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 240 192 240 192 0 0 0 0 0 0), upper := (rows 259 50 524 56 213 229 197 197 453 709), lower := (rows 259 50 524 56 16 32 64 128 256 512), losses := [] }

theorem upper_43 : Upper D R [258,48,520,48] 13 :=
  bound_sound D R [258,48,520,48] 13 bound_43
    ((Boolean.boundCheck_true D R [258,48,520,48] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 240 192 240 176 0 0 0 0 0 0), upper := (rows 259 50 524 73 244 244 244 244 500 756), lower := (rows 259 50 524 73 16 32 64 128 256 512), losses := [] }

theorem upper_44 : Upper D R [258,48,520,65] 13 :=
  bound_sound D R [258,48,520,65] 13 bound_44
    ((Boolean.boundCheck_true D R [258,48,520,65] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 240 192 240 176 0 0 0 0 0 0), upper := (rows 259 50 524 76 241 241 241 241 497 753), lower := (rows 259 50 524 76 16 32 64 128 256 512), losses := [] }

theorem upper_45 : Upper D R [258,48,520,68] 13 :=
  bound_sound D R [258,48,520,68] 13 bound_45
    ((Boolean.boundCheck_true D R [258,48,520,68] 13 bound_45).mp (by decide +kernel))

def bound_46 : Bound 10 := { allowed := (rows 240 192 240 160 0 0 0 0 0 0), upper := (rows 259 50 524 88 245 229 229 229 485 741), lower := (rows 259 50 524 88 16 32 64 128 256 512), losses := [] }

theorem upper_46 : Upper D R [258,48,520,80] 13 :=
  bound_sound D R [258,48,520,80] 13 bound_46
    ((Boolean.boundCheck_true D R [258,48,520,80] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 240 192 240 48 0 0 0 0 0 0), upper := (rows 259 50 524 200 245 245 245 245 501 757), lower := (rows 259 50 524 200 16 32 64 128 256 512), losses := [] }

theorem upper_47 : Upper D R [258,48,520,192] 13 :=
  bound_sound D R [258,48,520,192] 13 bound_47
    ((Boolean.boundCheck_true D R [258,48,520,192] 13 bound_47).mp (by decide +kernel))

def route_31 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_31 : Upper D R [258,48,520] 13 := by
  apply routed_branch D R [258,48,520] 13 (by decide) (choices 2) [5,17,20,48,65,68,80,192] route_31
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,48,520] (choices 2) [5,17,20,48,65,68,80,192] route_31).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_32
  · exact upper_41
  · exact upper_42
  · exact upper_43
  · exact upper_44
  · exact upper_45
  · exact upper_46
  · exact upper_47

def bound_48 : Bound 10 := { allowed := (rows 240 192 224 240 0 0 0 0 0 0), upper := (rows 259 50 532 237 253 237 237 237 493 749), lower := (rows 259 50 532 8 16 32 64 128 256 512), losses := [] }

theorem upper_48 : Upper D R [258,48,528] 13 :=
  bound_sound D R [258,48,528] 13 bound_48
    ((Boolean.boundCheck_true D R [258,48,528] 13 bound_48).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 240 192 176 240 0 0 0 0 0 0), upper := (rows 259 50 580 253 253 253 253 253 509 765), lower := (rows 259 50 580 8 16 32 64 128 256 512), losses := [] }

theorem upper_49 : Upper D R [258,48,576] 13 :=
  bound_sound D R [258,48,576] 13 bound_49
    ((Boolean.boundCheck_true D R [258,48,576] 13 bound_49).mp (by decide +kernel))

def route_0 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [258,48] 13 := by
  apply routed_branch D R [258,48] 13 (by decide) (choices 2) [9,17,24,48,65,72,80,192,513,520,528,576] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,48] (choices 2) [9,17,24,48,65,72,80,192,513,520,528,576] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_18
  · exact upper_19
  · exact upper_20
  · exact upper_21
  · exact upper_22
  · exact upper_23
  · exact upper_24
  · exact upper_25
  · exact upper_31
  · exact upper_48
  · exact upper_49

theorem upper : Upper D R [258,48] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case39
