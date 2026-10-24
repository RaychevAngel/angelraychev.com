import IrregularTen14Base

namespace Delivery.IrregularTen14.Case19
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 19 290 13 28 752 736 736 736 992 736), lower := (rows 19 290 13 28 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [18,288,9,20] 13 :=
  bound_sound D R [18,288,9,20] 13 bound_2
    ((Boolean.boundCheck_true D R [18,288,9,20] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 19 290 13 44 720 752 720 720 976 720), lower := (rows 19 290 13 44 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [18,288,9,36] 13 :=
  bound_sound D R [18,288,9,36] 13 bound_3
    ((Boolean.boundCheck_true D R [18,288,9,36] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 19 290 13 56 724 740 708 708 964 708), lower := (rows 19 290 13 56 16 32 64 128 256 512), losses := [] }

theorem upper_4 : Upper D R [18,288,9,48] 13 :=
  bound_sound D R [18,288,9,48] 13 bound_4
    ((Boolean.boundCheck_true D R [18,288,9,48] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 19 290 13 76 752 752 752 752 1008 752), lower := (rows 19 290 13 76 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [18,288,9,68] 13 :=
  bound_sound D R [18,288,9,68] 13 bound_5
    ((Boolean.boundCheck_true D R [18,288,9,68] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 19 290 13 88 756 740 740 740 996 740), lower := (rows 19 290 13 88 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [18,288,9,80] 13 :=
  bound_sound D R [18,288,9,80] 13 bound_6
    ((Boolean.boundCheck_true D R [18,288,9,80] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 19 290 13 104 724 756 724 724 980 724), lower := (rows 19 290 13 104 16 32 64 128 256 512), losses := [] }

theorem upper_7 : Upper D R [18,288,9,96] 13 :=
  bound_sound D R [18,288,9,96] 13 bound_7
    ((Boolean.boundCheck_true D R [18,288,9,96] 13 bound_7).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 19 290 13 200 756 756 756 756 1012 756), lower := (rows 19 290 13 200 16 32 64 128 256 512), losses := [] }

theorem upper_8 : Upper D R [18,288,9,192] 13 :=
  bound_sound D R [18,288,9,192] 13 bound_8
    ((Boolean.boundCheck_true D R [18,288,9,192] 13 bound_8).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 224 208 208 208 0 0 0 0 0 0), upper := (rows 19 290 13 524 48 240 208 208 464 720), lower := (rows 19 290 13 524 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 5 13 16 0 81 145 273 529), good := (rows 991 258 973 524 976 0 64 128 256 512) }] }

theorem upper_10 : Upper D R [18,288,9,516,32] 13 :=
  bound_sound D R [18,288,9,516,32] 13 bound_10
    ((Boolean.boundCheck_true D R [18,288,9,516,32] 13 bound_10).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 19 290 13 524 80 48 224 224 480 736), lower := (rows 19 290 13 524 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 34 5 9 0 32 98 162 290 546), good := (rows 975 994 13 524 64 994 64 128 256 512) }] }

theorem upper_12 : Upper D R [18,288,9,516,64,16] 13 :=
  bound_sound D R [18,288,9,516,64,16] 13 bound_12
    ((Boolean.boundCheck_true D R [18,288,9,516,64,16] 13 bound_12).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 19 290 13 524 80 96 240 176 432 688), lower := (rows 19 290 13 524 80 96 64 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 112 0 64 128 256 512), good := (rows 19 275 13 524 80 80 80 128 256 512) }] }

theorem upper_13 : Upper D R [18,288,9,516,64,64] 13 :=
  bound_sound D R [18,288,9,516,64,64] 13 bound_13
    ((Boolean.boundCheck_true D R [18,288,9,516,64,64] 13 bound_13).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 19 290 13 524 80 160 80 224 480 736), lower := (rows 19 290 13 524 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 83 5 9 0 241 64 208 336 592), good := (rows 943 290 47 524 994 160 994 160 256 512) }] }

theorem upper_15 : Upper D R [18,288,9,516,64,128,16] 13 :=
  bound_sound D R [18,288,9,516,64,128,16] 13 bound_15
    ((Boolean.boundCheck_true D R [18,288,9,516,64,128,16] 13 bound_15).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 224 208 208 208 0 0 0 0 0 0), upper := (rows 19 290 13 524 80 160 96 208 464 720), lower := (rows 19 290 13 524 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 2 5 9 80 0 64 208 336 592), good := (rows 927 258 13 524 976 128 976 128 256 512) }] }

theorem upper_16 : Upper D R [18,288,9,516,64,128,32] 13 :=
  bound_sound D R [18,288,9,516,64,128,32] 13 bound_16
    ((Boolean.boundCheck_true D R [18,288,9,516,64,128,32] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 19 290 13 524 80 160 192 240 368 624), lower := (rows 19 290 13 524 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 242 0 224 128 256 512), good := (rows 19 339 13 524 80 208 208 208 256 512) }] }

theorem upper_17 : Upper D R [18,288,9,516,64,128,128] 13 :=
  bound_sound D R [18,288,9,516,64,128,128] 13 bound_17
    ((Boolean.boundCheck_true D R [18,288,9,516,64,128,128] 13 bound_17).mp (by decide +kernel))

def route_14 : Route 10 := (fun mask => (mask,id))

theorem upper_14 : Upper D R [18,288,9,516,64,128] 13 := by
  apply routed_branch D R [18,288,9,516,64,128] 13 (by decide) (choices 1) [16,32,128] route_14
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,288,9,516,64,128] (choices 1) [16,32,128] route_14).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_15
  · exact upper_16
  · exact upper_17

def route_11 : Route 10 := (fun mask => (mask,id))

theorem upper_11 : Upper D R [18,288,9,516,64] 13 := by
  apply routed_branch D R [18,288,9,516,64] 13 (by decide) (choices 1) [16,64,128] route_11
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,288,9,516,64] (choices 1) [16,64,128] route_11).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_12
  · exact upper_13
  · exact upper_14

def route_9 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_9 : Upper D R [18,288,9,516] 13 := by
  apply routed_branch D R [18,288,9,516] 13 (by decide) (choices 1) [32,64] route_9
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,288,9,516] (choices 1) [32,64] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_10
  · exact upper_11

def bound_18 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 19 290 13 536 244 228 228 228 484 740), lower := (rows 19 290 13 536 16 32 64 128 256 512), losses := [] }

theorem upper_18 : Upper D R [18,288,9,528] 13 :=
  bound_sound D R [18,288,9,528] 13 bound_18
    ((Boolean.boundCheck_true D R [18,288,9,528] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 19 290 13 552 212 244 212 212 468 724), lower := (rows 19 290 13 552 16 32 64 128 256 512), losses := [] }

theorem upper_19 : Upper D R [18,288,9,544] 13 :=
  bound_sound D R [18,288,9,544] 13 bound_19
    ((Boolean.boundCheck_true D R [18,288,9,544] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 19 290 13 584 244 244 244 244 500 756), lower := (rows 19 290 13 584 16 32 64 128 256 512), losses := [] }

theorem upper_20 : Upper D R [18,288,9,576] 13 :=
  bound_sound D R [18,288,9,576] 13 bound_20
    ((Boolean.boundCheck_true D R [18,288,9,576] 13 bound_20).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [18,288,9] 13 := by
  apply routed_branch D R [18,288,9] 13 (by decide) (choices 2) [20,36,48,68,80,96,192,516,528,544,576] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,288,9] (choices 2) [20,36,48,68,80,96,192,516,528,544,576] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5
  · exact upper_6
  · exact upper_7
  · exact upper_8
  · exact upper_9
  · exact upper_18
  · exact upper_19
  · exact upper_20

def bound_21 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 19 290 21 748 764 748 748 748 1004 748), lower := (rows 19 290 21 8 16 32 64 128 256 512), losses := [] }

theorem upper_21 : Upper D R [18,288,17] 13 :=
  bound_sound D R [18,288,17] 13 bound_21
    ((Boolean.boundCheck_true D R [18,288,17] 13 bound_21).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 19 290 28 749 757 741 741 741 997 741), lower := (rows 19 290 28 8 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [18,288,24] 13 :=
  bound_sound D R [18,288,24] 13 bound_22
    ((Boolean.boundCheck_true D R [18,288,24] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 19 290 37 732 732 764 732 732 988 732), lower := (rows 19 290 37 8 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [18,288,33] 13 :=
  bound_sound D R [18,288,33] 13 bound_23
    ((Boolean.boundCheck_true D R [18,288,33] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 19 290 44 733 725 757 725 725 981 725), lower := (rows 19 290 44 8 16 32 64 128 256 512), losses := [] }

theorem upper_24 : Upper D R [18,288,40] 13 :=
  bound_sound D R [18,288,40] 13 bound_24
    ((Boolean.boundCheck_true D R [18,288,40] 13 bound_24).mp (by decide +kernel))

def bound_25 : Bound 10 := { allowed := (rows 224 208 192 240 0 0 0 0 0 0), upper := (rows 19 290 52 717 733 749 717 717 973 717), lower := (rows 19 290 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_25 : Upper D R [18,288,48] 13 :=
  bound_sound D R [18,288,48] 13 bound_25
    ((Boolean.boundCheck_true D R [18,288,48] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 19 290 69 764 764 764 764 764 1020 764), lower := (rows 19 290 69 8 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [18,288,65] 13 :=
  bound_sound D R [18,288,65] 13 bound_26
    ((Boolean.boundCheck_true D R [18,288,65] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 19 290 76 765 757 757 757 757 1013 757), lower := (rows 19 290 76 8 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [18,288,72] 13 :=
  bound_sound D R [18,288,72] 13 bound_27
    ((Boolean.boundCheck_true D R [18,288,72] 13 bound_27).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 224 208 160 240 0 0 0 0 0 0), upper := (rows 19 290 84 749 765 749 749 749 1005 749), lower := (rows 19 290 84 8 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [18,288,80] 13 :=
  bound_sound D R [18,288,80] 13 bound_28
    ((Boolean.boundCheck_true D R [18,288,80] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 224 208 144 240 0 0 0 0 0 0), upper := (rows 19 290 100 733 733 765 733 733 989 733), lower := (rows 19 290 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [18,288,96] 13 :=
  bound_sound D R [18,288,96] 13 bound_29
    ((Boolean.boundCheck_true D R [18,288,96] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 224 208 48 240 0 0 0 0 0 0), upper := (rows 19 290 196 765 765 765 765 765 1021 765), lower := (rows 19 290 196 8 16 32 64 128 256 512), losses := [] }

theorem upper_30 : Upper D R [18,288,192] 13 :=
  bound_sound D R [18,288,192] 13 bound_30
    ((Boolean.boundCheck_true D R [18,288,192] 13 bound_30).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 19 290 517 28 248 232 232 232 488 744), lower := (rows 19 290 517 28 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [18,288,513,20] 13 :=
  bound_sound D R [18,288,513,20] 13 bound_32
    ((Boolean.boundCheck_true D R [18,288,513,20] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 19 290 517 44 216 248 216 216 472 728), lower := (rows 19 290 517 44 16 32 64 128 256 512), losses := [] }

theorem upper_33 : Upper D R [18,288,513,36] 13 :=
  bound_sound D R [18,288,513,36] 13 bound_33
    ((Boolean.boundCheck_true D R [18,288,513,36] 13 bound_33).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 19 290 517 56 220 236 204 204 460 716), lower := (rows 19 290 517 56 16 32 64 128 256 512), losses := [] }

theorem upper_34 : Upper D R [18,288,513,48] 13 :=
  bound_sound D R [18,288,513,48] 13 bound_34
    ((Boolean.boundCheck_true D R [18,288,513,48] 13 bound_34).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 19 290 517 76 248 248 248 248 504 760), lower := (rows 19 290 517 76 16 32 64 128 256 512), losses := [] }

theorem upper_35 : Upper D R [18,288,513,68] 13 :=
  bound_sound D R [18,288,513,68] 13 bound_35
    ((Boolean.boundCheck_true D R [18,288,513,68] 13 bound_35).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 19 290 517 88 252 236 236 236 492 748), lower := (rows 19 290 517 88 16 32 64 128 256 512), losses := [] }

theorem upper_36 : Upper D R [18,288,513,80] 13 :=
  bound_sound D R [18,288,513,80] 13 bound_36
    ((Boolean.boundCheck_true D R [18,288,513,80] 13 bound_36).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 19 290 517 104 220 252 220 220 476 732), lower := (rows 19 290 517 104 16 32 64 128 256 512), losses := [] }

theorem upper_37 : Upper D R [18,288,513,96] 13 :=
  bound_sound D R [18,288,513,96] 13 bound_37
    ((Boolean.boundCheck_true D R [18,288,513,96] 13 bound_37).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 19 290 517 200 252 252 252 252 508 764), lower := (rows 19 290 517 200 16 32 64 128 256 512), losses := [] }

theorem upper_38 : Upper D R [18,288,513,192] 13 :=
  bound_sound D R [18,288,513,192] 13 bound_38
    ((Boolean.boundCheck_true D R [18,288,513,192] 13 bound_38).mp (by decide +kernel))

def route_31 : Route 10 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_31 : Upper D R [18,288,513] 13 := by
  apply routed_branch D R [18,288,513] 13 (by decide) (choices 2) [20,36,48,68,80,96,192] route_31
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,288,513] (choices 2) [20,36,48,68,80,96,192] route_31).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_32
  · exact upper_33
  · exact upper_34
  · exact upper_35
  · exact upper_36
  · exact upper_37
  · exact upper_38

def bound_41 : Bound 10 := { allowed := (rows 224 208 208 208 0 0 0 0 0 0), upper := (rows 19 290 524 13 48 240 208 208 464 720), lower := (rows 19 290 524 13 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 13 9 16 0 81 145 273 529), good := (rows 991 258 524 973 976 0 64 128 256 512) }] }

theorem upper_41 : Upper D R [18,288,520,5,32] 13 :=
  bound_sound D R [18,288,520,5,32] 13 bound_41
    ((Boolean.boundCheck_true D R [18,288,520,5,32] 13 bound_41).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 19 290 524 13 80 48 224 224 480 736), lower := (rows 19 290 524 13 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 34 5 9 0 32 98 162 290 546), good := (rows 975 994 524 13 64 994 64 128 256 512) }] }

theorem upper_43 : Upper D R [18,288,520,5,64,16] 13 :=
  bound_sound D R [18,288,520,5,64,16] 13 bound_43
    ((Boolean.boundCheck_true D R [18,288,520,5,64,16] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 19 290 524 13 80 96 240 176 432 688), lower := (rows 19 290 524 13 80 96 64 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 112 0 64 128 256 512), good := (rows 19 275 524 13 80 80 80 128 256 512) }] }

theorem upper_44 : Upper D R [18,288,520,5,64,64] 13 :=
  bound_sound D R [18,288,520,5,64,64] 13 bound_44
    ((Boolean.boundCheck_true D R [18,288,520,5,64,64] 13 bound_44).mp (by decide +kernel))

def bound_46 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 19 290 524 13 80 160 80 224 480 736), lower := (rows 19 290 524 13 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 83 5 9 0 241 64 208 336 592), good := (rows 943 290 524 47 994 160 994 160 256 512) }] }

theorem upper_46 : Upper D R [18,288,520,5,64,128,16] 13 :=
  bound_sound D R [18,288,520,5,64,128,16] 13 bound_46
    ((Boolean.boundCheck_true D R [18,288,520,5,64,128,16] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 224 208 208 208 0 0 0 0 0 0), upper := (rows 19 290 524 13 80 160 96 208 464 720), lower := (rows 19 290 524 13 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 2 5 9 80 0 64 208 336 592), good := (rows 927 258 524 13 976 128 976 128 256 512) }] }

theorem upper_47 : Upper D R [18,288,520,5,64,128,32] 13 :=
  bound_sound D R [18,288,520,5,64,128,32] 13 bound_47
    ((Boolean.boundCheck_true D R [18,288,520,5,64,128,32] 13 bound_47).mp (by decide +kernel))

def bound_48 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 19 290 524 13 80 160 192 240 368 624), lower := (rows 19 290 524 13 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 242 0 224 128 256 512), good := (rows 19 339 524 13 80 208 208 208 256 512) }] }

theorem upper_48 : Upper D R [18,288,520,5,64,128,128] 13 :=
  bound_sound D R [18,288,520,5,64,128,128] 13 bound_48
    ((Boolean.boundCheck_true D R [18,288,520,5,64,128,128] 13 bound_48).mp (by decide +kernel))

def route_45 : Route 10 := (fun mask => (mask,id))

theorem upper_45 : Upper D R [18,288,520,5,64,128] 13 := by
  apply routed_branch D R [18,288,520,5,64,128] 13 (by decide) (choices 1) [16,32,128] route_45
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,288,520,5,64,128] (choices 1) [16,32,128] route_45).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_46
  · exact upper_47
  · exact upper_48

def route_42 : Route 10 := (fun mask => (mask,id))

theorem upper_42 : Upper D R [18,288,520,5,64] 13 := by
  apply routed_branch D R [18,288,520,5,64] 13 (by decide) (choices 1) [16,64,128] route_42
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,288,520,5,64] (choices 1) [16,64,128] route_42).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_43
  · exact upper_44
  · exact upper_45

def route_40 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_40 : Upper D R [18,288,520,5] 13 := by
  apply routed_branch D R [18,288,520,5] 13 (by decide) (choices 1) [32,64] route_40
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,288,520,5] (choices 1) [32,64] route_40).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_41
  · exact upper_42

def bound_49 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 19 290 524 25 244 228 228 228 484 740), lower := (rows 19 290 524 25 16 32 64 128 256 512), losses := [] }

theorem upper_49 : Upper D R [18,288,520,17] 13 :=
  bound_sound D R [18,288,520,17] 13 bound_49
    ((Boolean.boundCheck_true D R [18,288,520,17] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 19 290 524 28 241 225 225 225 481 737), lower := (rows 19 290 524 28 16 32 64 128 256 512), losses := [] }

theorem upper_50 : Upper D R [18,288,520,20] 13 :=
  bound_sound D R [18,288,520,20] 13 bound_50
    ((Boolean.boundCheck_true D R [18,288,520,20] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 19 290 524 41 212 244 212 212 468 724), lower := (rows 19 290 524 41 16 32 64 128 256 512), losses := [] }

theorem upper_51 : Upper D R [18,288,520,33] 13 :=
  bound_sound D R [18,288,520,33] 13 bound_51
    ((Boolean.boundCheck_true D R [18,288,520,33] 13 bound_51).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 19 290 524 44 209 241 209 209 465 721), lower := (rows 19 290 524 44 16 32 64 128 256 512), losses := [] }

theorem upper_52 : Upper D R [18,288,520,36] 13 :=
  bound_sound D R [18,288,520,36] 13 bound_52
    ((Boolean.boundCheck_true D R [18,288,520,36] 13 bound_52).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 19 290 524 56 213 229 197 197 453 709), lower := (rows 19 290 524 56 16 32 64 128 256 512), losses := [] }

theorem upper_53 : Upper D R [18,288,520,48] 13 :=
  bound_sound D R [18,288,520,48] 13 bound_53
    ((Boolean.boundCheck_true D R [18,288,520,48] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 19 290 524 73 244 244 244 244 500 756), lower := (rows 19 290 524 73 16 32 64 128 256 512), losses := [] }

theorem upper_54 : Upper D R [18,288,520,65] 13 :=
  bound_sound D R [18,288,520,65] 13 bound_54
    ((Boolean.boundCheck_true D R [18,288,520,65] 13 bound_54).mp (by decide +kernel))

def bound_55 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 19 290 524 76 241 241 241 241 497 753), lower := (rows 19 290 524 76 16 32 64 128 256 512), losses := [] }

theorem upper_55 : Upper D R [18,288,520,68] 13 :=
  bound_sound D R [18,288,520,68] 13 bound_55
    ((Boolean.boundCheck_true D R [18,288,520,68] 13 bound_55).mp (by decide +kernel))

def bound_56 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 19 290 524 88 245 229 229 229 485 741), lower := (rows 19 290 524 88 16 32 64 128 256 512), losses := [] }

theorem upper_56 : Upper D R [18,288,520,80] 13 :=
  bound_sound D R [18,288,520,80] 13 bound_56
    ((Boolean.boundCheck_true D R [18,288,520,80] 13 bound_56).mp (by decide +kernel))

def bound_57 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 19 290 524 104 213 245 213 213 469 725), lower := (rows 19 290 524 104 16 32 64 128 256 512), losses := [] }

theorem upper_57 : Upper D R [18,288,520,96] 13 :=
  bound_sound D R [18,288,520,96] 13 bound_57
    ((Boolean.boundCheck_true D R [18,288,520,96] 13 bound_57).mp (by decide +kernel))

def bound_58 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 19 290 524 200 245 245 245 245 501 757), lower := (rows 19 290 524 200 16 32 64 128 256 512), losses := [] }

theorem upper_58 : Upper D R [18,288,520,192] 13 :=
  bound_sound D R [18,288,520,192] 13 bound_58
    ((Boolean.boundCheck_true D R [18,288,520,192] 13 bound_58).mp (by decide +kernel))

def route_39 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_39 : Upper D R [18,288,520] 13 := by
  apply routed_branch D R [18,288,520] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192] route_39
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,288,520] (choices 2) [5,17,20,33,36,48,65,68,80,96,192] route_39).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_40
  · exact upper_49
  · exact upper_50
  · exact upper_51
  · exact upper_52
  · exact upper_53
  · exact upper_54
  · exact upper_55
  · exact upper_56
  · exact upper_57
  · exact upper_58

def bound_59 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 19 290 532 237 253 237 237 237 493 749), lower := (rows 19 290 532 8 16 32 64 128 256 512), losses := [] }

theorem upper_59 : Upper D R [18,288,528] 13 :=
  bound_sound D R [18,288,528] 13 bound_59
    ((Boolean.boundCheck_true D R [18,288,528] 13 bound_59).mp (by decide +kernel))

def bound_60 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 19 290 548 221 221 253 221 221 477 733), lower := (rows 19 290 548 8 16 32 64 128 256 512), losses := [] }

theorem upper_60 : Upper D R [18,288,544] 13 :=
  bound_sound D R [18,288,544] 13 bound_60
    ((Boolean.boundCheck_true D R [18,288,544] 13 bound_60).mp (by decide +kernel))

def bound_61 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 19 290 580 253 253 253 253 253 509 765), lower := (rows 19 290 580 8 16 32 64 128 256 512), losses := [] }

theorem upper_61 : Upper D R [18,288,576] 13 :=
  bound_sound D R [18,288,576] 13 bound_61
    ((Boolean.boundCheck_true D R [18,288,576] 13 bound_61).mp (by decide +kernel))

def route_0 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [18,288] 13 := by
  apply routed_branch D R [18,288] 13 (by decide) (choices 2) [9,17,24,33,40,48,65,72,80,96,192,513,520,528,544,576] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,288] (choices 2) [9,17,24,33,40,48,65,72,80,96,192,513,520,528,544,576] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_21
  · exact upper_22
  · exact upper_23
  · exact upper_24
  · exact upper_25
  · exact upper_26
  · exact upper_27
  · exact upper_28
  · exact upper_29
  · exact upper_30
  · exact upper_31
  · exact upper_39
  · exact upper_59
  · exact upper_60
  · exact upper_61

theorem upper : Upper D R [18,288] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case19
