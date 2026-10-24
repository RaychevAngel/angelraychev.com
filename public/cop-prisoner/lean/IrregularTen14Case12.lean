import IrregularTen14Base

namespace Delivery.IrregularTen14.Case12
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_1 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 19 35 28 1004 1012 996 996 996 996 996), lower := (rows 19 35 28 8 16 32 64 128 256 512), losses := [] }

theorem upper_1 : Upper D R [18,33,24] 13 :=
  bound_sound D R [18,33,24] 13 bound_1
    ((Boolean.boundCheck_true D R [18,33,24] 13 bound_1).mp (by decide +kernel))

def bound_2 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 19 35 44 988 980 1012 980 980 980 980), lower := (rows 19 35 44 8 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [18,33,40] 13 :=
  bound_sound D R [18,33,40] 13 bound_2
    ((Boolean.boundCheck_true D R [18,33,40] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 208 192 240 0 0 0 0 0 0), upper := (rows 19 35 52 972 988 1004 972 972 972 972), lower := (rows 19 35 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [18,33,48] 13 :=
  bound_sound D R [18,33,48] 13 bound_3
    ((Boolean.boundCheck_true D R [18,33,48] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 19 35 76 1020 1012 1012 1012 1012 1012 1012), lower := (rows 19 35 76 8 16 32 64 128 256 512), losses := [] }

theorem upper_4 : Upper D R [18,33,72] 13 :=
  bound_sound D R [18,33,72] 13 bound_4
    ((Boolean.boundCheck_true D R [18,33,72] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 224 208 160 240 0 0 0 0 0 0), upper := (rows 19 35 84 1004 1020 1004 1004 1004 1004 1004), lower := (rows 19 35 84 8 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [18,33,80] 13 :=
  bound_sound D R [18,33,80] 13 bound_5
    ((Boolean.boundCheck_true D R [18,33,80] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 224 208 144 240 0 0 0 0 0 0), upper := (rows 19 35 100 988 988 1020 988 988 988 988), lower := (rows 19 35 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [18,33,96] 13 :=
  bound_sound D R [18,33,96] 13 bound_6
    ((Boolean.boundCheck_true D R [18,33,96] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 224 208 48 240 0 0 0 0 0 0), upper := (rows 19 35 196 1020 1020 1020 1020 1020 1020 1020), lower := (rows 19 35 196 8 16 32 64 128 256 512), losses := [] }

theorem upper_7 : Upper D R [18,33,192] 13 :=
  bound_sound D R [18,33,192] 13 bound_7
    ((Boolean.boundCheck_true D R [18,33,192] 13 bound_7).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 19 35 268 28 752 736 736 736 992 736), lower := (rows 19 35 268 28 16 32 64 128 256 512), losses := [] }

theorem upper_9 : Upper D R [18,33,264,20] 13 :=
  bound_sound D R [18,33,264,20] 13 bound_9
    ((Boolean.boundCheck_true D R [18,33,264,20] 13 bound_9).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 19 35 268 44 720 752 720 720 976 720), lower := (rows 19 35 268 44 16 32 64 128 256 512), losses := [] }

theorem upper_10 : Upper D R [18,33,264,36] 13 :=
  bound_sound D R [18,33,264,36] 13 bound_10
    ((Boolean.boundCheck_true D R [18,33,264,36] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 19 35 268 56 724 740 708 708 964 708), lower := (rows 19 35 268 56 16 32 64 128 256 512), losses := [] }

theorem upper_11 : Upper D R [18,33,264,48] 13 :=
  bound_sound D R [18,33,264,48] 13 bound_11
    ((Boolean.boundCheck_true D R [18,33,264,48] 13 bound_11).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 19 35 268 76 752 752 752 752 1008 752), lower := (rows 19 35 268 76 16 32 64 128 256 512), losses := [] }

theorem upper_12 : Upper D R [18,33,264,68] 13 :=
  bound_sound D R [18,33,264,68] 13 bound_12
    ((Boolean.boundCheck_true D R [18,33,264,68] 13 bound_12).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 19 35 268 88 756 740 740 740 996 740), lower := (rows 19 35 268 88 16 32 64 128 256 512), losses := [] }

theorem upper_13 : Upper D R [18,33,264,80] 13 :=
  bound_sound D R [18,33,264,80] 13 bound_13
    ((Boolean.boundCheck_true D R [18,33,264,80] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 19 35 268 104 724 756 724 724 980 724), lower := (rows 19 35 268 104 16 32 64 128 256 512), losses := [] }

theorem upper_14 : Upper D R [18,33,264,96] 13 :=
  bound_sound D R [18,33,264,96] 13 bound_14
    ((Boolean.boundCheck_true D R [18,33,264,96] 13 bound_14).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 19 35 268 200 756 756 756 756 1012 756), lower := (rows 19 35 268 200 16 32 64 128 256 512), losses := [] }

theorem upper_15 : Upper D R [18,33,264,192] 13 :=
  bound_sound D R [18,33,264,192] 13 bound_15
    ((Boolean.boundCheck_true D R [18,33,264,192] 13 bound_15).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 224 208 208 208 0 0 0 0 0 0), upper := (rows 19 35 268 524 48 240 208 208 464 720), lower := (rows 19 35 268 524 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 23 27 16 0 81 145 273 529), good := (rows 991 975 268 524 988 0 64 128 256 512) }] }

theorem upper_17 : Upper D R [18,33,264,516,32] 13 :=
  bound_sound D R [18,33,264,516,32] 13 bound_17
    ((Boolean.boundCheck_true D R [18,33,264,516,32] 13 bound_17).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 224 208 224 224 0 0 0 0 0 0), upper := (rows 19 35 268 524 80 48 224 224 480 736), lower := (rows 19 35 268 524 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 39 43 0 32 98 162 290 546), good := (rows 975 1007 268 524 64 1004 64 128 256 512) }] }

theorem upper_19 : Upper D R [18,33,264,516,64,16] 13 :=
  bound_sound D R [18,33,264,516,64,16] 13 bound_19
    ((Boolean.boundCheck_true D R [18,33,264,516,64,16] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 224 192 240 240 0 0 0 0 0 0), upper := (rows 19 35 268 524 80 96 240 176 432 688), lower := (rows 19 35 268 524 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 1 3 4 8 0 112 64 128 256 512), good := (rows 35 35 268 524 96 96 96 128 256 512) }] }

theorem upper_20 : Upper D R [18,33,264,516,64,64] 13 :=
  bound_sound D R [18,33,264,516,64,64] 13 bound_20
    ((Boolean.boundCheck_true D R [18,33,264,516,64,64] 13 bound_20).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 224 192 224 224 0 0 0 0 0 0), upper := (rows 19 35 268 524 80 160 80 224 480 736), lower := (rows 19 35 268 524 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 85 89 0 241 64 208 336 592), good := (rows 943 47 268 524 1004 160 1004 160 256 512) }] }

theorem upper_22 : Upper D R [18,33,264,516,64,128,16] 13 :=
  bound_sound D R [18,33,264,516,64,128,16] 13 bound_22
    ((Boolean.boundCheck_true D R [18,33,264,516,64,128,16] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 224 208 208 208 0 0 0 0 0 0), upper := (rows 19 35 268 524 80 160 96 208 464 720), lower := (rows 19 35 268 524 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 2 85 89 80 0 64 208 336 592), good := (rows 927 15 268 524 988 128 988 128 256 512) }] }

theorem upper_23 : Upper D R [18,33,264,516,64,128,32] 13 :=
  bound_sound D R [18,33,264,516,64,128,32] 13 bound_23
    ((Boolean.boundCheck_true D R [18,33,264,516,64,128,32] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 192 208 240 240 0 0 0 0 0 0), upper := (rows 19 35 268 524 80 160 192 240 368 624), lower := (rows 19 35 268 524 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 242 0 224 128 256 512), good := (rows 19 83 268 524 80 208 208 208 256 512) }] }

theorem upper_24 : Upper D R [18,33,264,516,64,128,128] 13 :=
  bound_sound D R [18,33,264,516,64,128,128] 13 bound_24
    ((Boolean.boundCheck_true D R [18,33,264,516,64,128,128] 13 bound_24).mp (by decide +kernel))

def route_21 : Route 10 := (fun mask => (mask,id))

theorem upper_21 : Upper D R [18,33,264,516,64,128] 13 := by
  apply routed_branch D R [18,33,264,516,64,128] 13 (by decide) (choices 1) [16,32,128] route_21
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,33,264,516,64,128] (choices 1) [16,32,128] route_21).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_22
  · exact upper_23
  · exact upper_24

def route_18 : Route 10 := (fun mask => (mask,id))

theorem upper_18 : Upper D R [18,33,264,516,64] 13 := by
  apply routed_branch D R [18,33,264,516,64] 13 (by decide) (choices 1) [16,64,128] route_18
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,33,264,516,64] (choices 1) [16,64,128] route_18).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_19
  · exact upper_20
  · exact upper_21

def route_16 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_16 : Upper D R [18,33,264,516] 13 := by
  apply routed_branch D R [18,33,264,516] 13 (by decide) (choices 1) [32,64] route_16
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,33,264,516] (choices 1) [32,64] route_16).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_17
  · exact upper_18

def bound_25 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 19 35 268 536 244 228 228 228 484 740), lower := (rows 19 35 268 536 16 32 64 128 256 512), losses := [] }

theorem upper_25 : Upper D R [18,33,264,528] 13 :=
  bound_sound D R [18,33,264,528] 13 bound_25
    ((Boolean.boundCheck_true D R [18,33,264,528] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 19 35 268 552 212 244 212 212 468 724), lower := (rows 19 35 268 552 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [18,33,264,544] 13 :=
  bound_sound D R [18,33,264,544] 13 bound_26
    ((Boolean.boundCheck_true D R [18,33,264,544] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 19 35 268 584 244 244 244 244 500 756), lower := (rows 19 35 268 584 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [18,33,264,576] 13 :=
  bound_sound D R [18,33,264,576] 13 bound_27
    ((Boolean.boundCheck_true D R [18,33,264,576] 13 bound_27).mp (by decide +kernel))

def route_8 : Route 10 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_8 : Upper D R [18,33,264] 13 := by
  apply routed_branch D R [18,33,264] 13 (by decide) (choices 2) [20,36,48,68,80,96,192,516,528,544,576] route_8
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,33,264] (choices 2) [20,36,48,68,80,96,192,516,528,544,576] route_8).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_9
  · exact upper_10
  · exact upper_11
  · exact upper_12
  · exact upper_13
  · exact upper_14
  · exact upper_15
  · exact upper_16
  · exact upper_25
  · exact upper_26
  · exact upper_27

def bound_28 : Bound 10 := { allowed := (rows 224 208 224 240 0 0 0 0 0 0), upper := (rows 19 35 276 748 764 748 748 748 1004 748), lower := (rows 19 35 276 8 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [18,33,272] 13 :=
  bound_sound D R [18,33,272] 13 bound_28
    ((Boolean.boundCheck_true D R [18,33,272] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 224 208 208 240 0 0 0 0 0 0), upper := (rows 19 35 292 732 732 764 732 732 988 732), lower := (rows 19 35 292 8 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [18,33,288] 13 :=
  bound_sound D R [18,33,288] 13 bound_29
    ((Boolean.boundCheck_true D R [18,33,288] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 224 208 176 240 0 0 0 0 0 0), upper := (rows 19 35 324 764 764 764 764 764 1020 764), lower := (rows 19 35 324 8 16 32 64 128 256 512), losses := [] }

theorem upper_30 : Upper D R [18,33,320] 13 :=
  bound_sound D R [18,33,320] 13 bound_30
    ((Boolean.boundCheck_true D R [18,33,320] 13 bound_30).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 224 208 240 224 0 0 0 0 0 0), upper := (rows 19 35 772 28 248 232 232 232 488 744), lower := (rows 19 35 772 28 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [18,33,768,20] 13 :=
  bound_sound D R [18,33,768,20] 13 bound_32
    ((Boolean.boundCheck_true D R [18,33,768,20] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 224 208 240 208 0 0 0 0 0 0), upper := (rows 19 35 772 44 216 248 216 216 472 728), lower := (rows 19 35 772 44 16 32 64 128 256 512), losses := [] }

theorem upper_33 : Upper D R [18,33,768,36] 13 :=
  bound_sound D R [18,33,768,36] 13 bound_33
    ((Boolean.boundCheck_true D R [18,33,768,36] 13 bound_33).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 224 208 240 192 0 0 0 0 0 0), upper := (rows 19 35 772 56 220 236 204 204 460 716), lower := (rows 19 35 772 56 16 32 64 128 256 512), losses := [] }

theorem upper_34 : Upper D R [18,33,768,48] 13 :=
  bound_sound D R [18,33,768,48] 13 bound_34
    ((Boolean.boundCheck_true D R [18,33,768,48] 13 bound_34).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 224 208 240 176 0 0 0 0 0 0), upper := (rows 19 35 772 76 248 248 248 248 504 760), lower := (rows 19 35 772 76 16 32 64 128 256 512), losses := [] }

theorem upper_35 : Upper D R [18,33,768,68] 13 :=
  bound_sound D R [18,33,768,68] 13 bound_35
    ((Boolean.boundCheck_true D R [18,33,768,68] 13 bound_35).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 224 208 240 160 0 0 0 0 0 0), upper := (rows 19 35 772 88 252 236 236 236 492 748), lower := (rows 19 35 772 88 16 32 64 128 256 512), losses := [] }

theorem upper_36 : Upper D R [18,33,768,80] 13 :=
  bound_sound D R [18,33,768,80] 13 bound_36
    ((Boolean.boundCheck_true D R [18,33,768,80] 13 bound_36).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 224 208 240 144 0 0 0 0 0 0), upper := (rows 19 35 772 104 220 252 220 220 476 732), lower := (rows 19 35 772 104 16 32 64 128 256 512), losses := [] }

theorem upper_37 : Upper D R [18,33,768,96] 13 :=
  bound_sound D R [18,33,768,96] 13 bound_37
    ((Boolean.boundCheck_true D R [18,33,768,96] 13 bound_37).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 224 208 240 48 0 0 0 0 0 0), upper := (rows 19 35 772 200 252 252 252 252 508 764), lower := (rows 19 35 772 200 16 32 64 128 256 512), losses := [] }

theorem upper_38 : Upper D R [18,33,768,192] 13 :=
  bound_sound D R [18,33,768,192] 13 bound_38
    ((Boolean.boundCheck_true D R [18,33,768,192] 13 bound_38).mp (by decide +kernel))

def route_31 : Route 10 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_31 : Upper D R [18,33,768] 13 := by
  apply routed_branch D R [18,33,768] 13 (by decide) (choices 2) [20,36,48,68,80,96,192] route_31
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,33,768] (choices 2) [20,36,48,68,80,96,192] route_31).mp (by decide +kernel))
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

def route_0 : Route 10 := (fun mask => match mask with | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 520 => (264,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [18,33] 13 := by
  apply routed_branch D R [18,33] 13 (by decide) (choices 2) [24,40,48,72,80,96,192,264,272,288,320,768] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,33] (choices 2) [24,40,48,72,80,96,192,264,272,288,320,768] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5
  · exact upper_6
  · exact upper_7
  · exact upper_8
  · exact upper_28
  · exact upper_29
  · exact upper_30
  · exact upper_31

theorem upper : Upper D R [18,33] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case12
