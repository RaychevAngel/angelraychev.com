import IrregularTen14Base

namespace Delivery.IrregularTen14.Case16
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 19 259 28 44 752 736 736 736 992 736), lower := (rows 19 259 28 44 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [18,257,24,36] 13 :=
  bound_sound D R [18,257,24,36] 13 bound_2
    ((Boolean.boundCheck_true D R [18,257,24,36] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 19 259 28 104 756 740 740 740 996 740), lower := (rows 19 259 28 104 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [18,257,24,96] 13 :=
  bound_sound D R [18,257,24,96] 13 bound_3
    ((Boolean.boundCheck_true D R [18,257,24,96] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 19 259 28 524 240 224 224 224 480 736), lower := (rows 19 259 28 524 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 3 4 12 0 1023 1023 1023 1023 1023), good := (rows 995 995 1004 1004 992 992 992 992 992 992) }] }

theorem upper_4 : Upper D R [18,257,24,516] 13 :=
  bound_sound D R [18,257,24,516] 13 bound_4
    ((Boolean.boundCheck_true D R [18,257,24,516] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 19 259 28 552 244 228 228 228 484 740), lower := (rows 19 259 28 552 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [18,257,24,544] 13 :=
  bound_sound D R [18,257,24,544] 13 bound_5
    ((Boolean.boundCheck_true D R [18,257,24,544] 13 bound_5).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [18,257,24] 13 := by
  apply routed_branch D R [18,257,24] 13 (by decide) (choices 2) [36,96,516,544] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,257,24] (choices 2) [36,96,516,544] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5

def bound_7 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 19 259 44 28 752 736 736 736 992 736), lower := (rows 19 259 44 28 16 32 64 128 256 512), losses := [] }

theorem upper_7 : Upper D R [18,257,40,20] 13 :=
  bound_sound D R [18,257,40,20] 13 bound_7
    ((Boolean.boundCheck_true D R [18,257,40,20] 13 bound_7).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 259 44 44 720 752 720 720 976 720), lower := (rows 19 259 44 44 16 32 64 128 256 512), losses := [] }

theorem upper_8 : Upper D R [18,257,40,36] 13 :=
  bound_sound D R [18,257,40,36] 13 bound_8
    ((Boolean.boundCheck_true D R [18,257,40,36] 13 bound_8).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 19 259 44 56 724 740 708 708 964 708), lower := (rows 19 259 44 56 16 32 64 128 256 512), losses := [] }

theorem upper_9 : Upper D R [18,257,40,48] 13 :=
  bound_sound D R [18,257,40,48] 13 bound_9
    ((Boolean.boundCheck_true D R [18,257,40,48] 13 bound_9).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 19 259 44 76 752 752 752 752 1008 752), lower := (rows 19 259 44 76 16 32 64 128 256 512), losses := [] }

theorem upper_10 : Upper D R [18,257,40,68] 13 :=
  bound_sound D R [18,257,40,68] 13 bound_10
    ((Boolean.boundCheck_true D R [18,257,40,68] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 19 259 44 88 756 740 740 740 996 740), lower := (rows 19 259 44 88 16 32 64 128 256 512), losses := [] }

theorem upper_11 : Upper D R [18,257,40,80] 13 :=
  bound_sound D R [18,257,40,80] 13 bound_11
    ((Boolean.boundCheck_true D R [18,257,40,80] 13 bound_11).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 19 259 44 104 724 756 724 724 980 724), lower := (rows 19 259 44 104 16 32 64 128 256 512), losses := [] }

theorem upper_12 : Upper D R [18,257,40,96] 13 :=
  bound_sound D R [18,257,40,96] 13 bound_12
    ((Boolean.boundCheck_true D R [18,257,40,96] 13 bound_12).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 19 259 44 200 756 756 756 756 1012 756), lower := (rows 19 259 44 200 16 32 64 128 256 512), losses := [] }

theorem upper_13 : Upper D R [18,257,40,192] 13 :=
  bound_sound D R [18,257,40,192] 13 bound_13
    ((Boolean.boundCheck_true D R [18,257,40,192] 13 bound_13).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 192 208 208 240 0 0 0 0 0 0), upper := (rows 19 259 44 524 48 240 208 208 464 720), lower := (rows 19 259 44 524 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 19 4 8 16 0 81 145 273 529), good := (rows 979 963 12 524 979 0 64 128 256 512) }] }

theorem upper_15 : Upper D R [18,257,40,516,32] 13 :=
  bound_sound D R [18,257,40,516,32] 13 bound_15
    ((Boolean.boundCheck_true D R [18,257,40,516,32] 13 bound_15).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 224 240 192 224 0 0 0 0 0 0), upper := (rows 19 259 44 524 80 48 224 224 480 736), lower := (rows 19 259 44 524 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 36 44 0 32 100 164 292 548), good := (rows 3 259 1004 972 64 1004 64 128 256 512) }] }

theorem upper_17 : Upper D R [18,257,40,516,64,16] 13 :=
  bound_sound D R [18,257,40,516,64,16] 13 bound_17
    ((Boolean.boundCheck_true D R [18,257,40,516,64,16] 13 bound_17).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 19 259 44 524 80 96 80 160 416 672), lower := (rows 19 259 44 524 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 117 127 0 112 64 245 373 629), good := (rows 943 911 940 908 1004 1004 1004 128 256 512) }] }

theorem upper_19 : Upper D R [18,257,40,516,64,64,16] 13 :=
  bound_sound D R [18,257,40,516,64,64,16] 13 bound_19
    ((Boolean.boundCheck_true D R [18,257,40,516,64,64,16] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 224 240 192 224 0 0 0 0 0 0), upper := (rows 19 259 44 524 80 96 96 144 400 656), lower := (rows 19 259 44 524 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 524 520 0 1023 1023 128 256 512), good := (rows 99 355 108 620 96 96 96 224 352 620) }] }

theorem upper_20 : Upper D R [18,257,40,516,64,64,32] 13 :=
  bound_sound D R [18,257,40,516,64,64,32] 13 bound_20
    ((Boolean.boundCheck_true D R [18,257,40,516,64,64,32] 13 bound_20).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 224 240 192 224 0 0 0 0 0 0), upper := (rows 19 259 44 524 80 96 192 144 416 672), lower := (rows 19 259 44 524 80 96 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 245 248 0 240 192 128 448 704), good := (rows 47 263 44 524 876 876 1004 1004 256 512) }] }

theorem upper_22 : Upper D R [18,257,40,516,64,64,128,16] 13 :=
  bound_sound D R [18,257,40,516,64,64,128,16] 13 bound_22
    ((Boolean.boundCheck_true D R [18,257,40,516,64,64,128,16] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 224 240 192 224 0 0 0 0 0 0), upper := (rows 19 259 44 524 80 96 192 160 400 656), lower := (rows 19 259 44 524 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 524 520 0 1023 1023 1023 256 512), good := (rows 227 483 236 748 224 224 224 224 480 748) }] }

theorem upper_23 : Upper D R [18,257,40,516,64,64,128,32] 13 :=
  bound_sound D R [18,257,40,516,64,64,128,32] 13 bound_23
    ((Boolean.boundCheck_true D R [18,257,40,516,64,64,128,32] 13 bound_23).mp (by decide +kernel))

def route_21 : Route 10 := (fun mask => (mask,id))

theorem upper_21 : Upper D R [18,257,40,516,64,64,128] 13 := by
  apply routed_branch D R [18,257,40,516,64,64,128] 13 (by decide) (choices 1) [16,32] route_21
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,257,40,516,64,64,128] (choices 1) [16,32] route_21).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_22
  · exact upper_23

def route_18 : Route 10 := (fun mask => (mask,id))

theorem upper_18 : Upper D R [18,257,40,516,64,64] 13 := by
  apply routed_branch D R [18,257,40,516,64,64] 13 (by decide) (choices 1) [16,32,128] route_18
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,257,40,516,64,64] (choices 1) [16,32,128] route_18).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_19
  · exact upper_20
  · exact upper_21

def bound_25 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 19 259 44 524 80 160 80 224 480 736), lower := (rows 19 259 44 524 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 87 89 0 241 64 208 336 592), good := (rows 943 303 44 524 1004 160 1004 160 256 512) }] }

theorem upper_25 : Upper D R [18,257,40,516,64,128,16] 13 :=
  bound_sound D R [18,257,40,516,64,128,16] 13 bound_25
    ((Boolean.boundCheck_true D R [18,257,40,516,64,128,16] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 192 208 208 240 0 0 0 0 0 0), upper := (rows 19 259 44 524 80 160 96 208 464 720), lower := (rows 19 259 44 524 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 83 4 8 80 0 64 208 336 592), good := (rows 915 259 12 524 979 128 979 128 256 512) }] }

theorem upper_26 : Upper D R [18,257,40,516,64,128,32] 13 :=
  bound_sound D R [18,257,40,516,64,128,32] 13 bound_26
    ((Boolean.boundCheck_true D R [18,257,40,516,64,128,32] 13 bound_26).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 19 259 44 524 80 160 192 144 352 608), lower := (rows 19 259 44 524 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 3 244 253 0 224 224 128 500 756), good := (rows 783 267 876 780 876 1004 1004 1004 256 512) }] }

theorem upper_28 : Upper D R [18,257,40,516,64,128,128,16] 13 :=
  bound_sound D R [18,257,40,516,64,128,128,16] 13 bound_28
    ((Boolean.boundCheck_true D R [18,257,40,516,64,128,128,16] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 224 240 192 224 0 0 0 0 0 0), upper := (rows 19 259 44 524 80 160 192 160 336 592), lower := (rows 19 259 44 524 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 524 520 0 1023 1023 1023 256 512), good := (rows 227 483 236 748 224 224 224 224 480 748) }] }

theorem upper_29 : Upper D R [18,257,40,516,64,128,128,32] 13 :=
  bound_sound D R [18,257,40,516,64,128,128,32] 13 bound_29
    ((Boolean.boundCheck_true D R [18,257,40,516,64,128,128,32] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 224 240 192 224 0 0 0 0 0 0), upper := (rows 19 259 44 524 80 160 192 192 304 560), lower := (rows 19 259 44 524 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 524 520 0 1023 1023 1023 256 512), good := (rows 227 483 236 748 224 224 224 224 480 748) }] }

theorem upper_30 : Upper D R [18,257,40,516,64,128,128,64] 13 :=
  bound_sound D R [18,257,40,516,64,128,128,64] 13 bound_30
    ((Boolean.boundCheck_true D R [18,257,40,516,64,128,128,64] 13 bound_30).mp (by decide +kernel))

def route_27 : Route 10 := (fun mask => (mask,id))

theorem upper_27 : Upper D R [18,257,40,516,64,128,128] 13 := by
  apply routed_branch D R [18,257,40,516,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_27
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,257,40,516,64,128,128] (choices 1) [16,32,64] route_27).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_28
  · exact upper_29
  · exact upper_30

def route_24 : Route 10 := (fun mask => (mask,id))

theorem upper_24 : Upper D R [18,257,40,516,64,128] 13 := by
  apply routed_branch D R [18,257,40,516,64,128] 13 (by decide) (choices 1) [16,32,128] route_24
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,257,40,516,64,128] (choices 1) [16,32,128] route_24).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_25
  · exact upper_26
  · exact upper_27

def route_16 : Route 10 := (fun mask => (mask,id))

theorem upper_16 : Upper D R [18,257,40,516,64] 13 := by
  apply routed_branch D R [18,257,40,516,64] 13 (by decide) (choices 1) [16,64,128] route_16
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,257,40,516,64] (choices 1) [16,64,128] route_16).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_17
  · exact upper_18
  · exact upper_24

def route_14 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_14 : Upper D R [18,257,40,516] 13 := by
  apply routed_branch D R [18,257,40,516] 13 (by decide) (choices 1) [32,64] route_14
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,257,40,516] (choices 1) [32,64] route_14).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_15
  · exact upper_16

def bound_31 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 19 259 44 536 244 228 228 228 484 740), lower := (rows 19 259 44 536 16 32 64 128 256 512), losses := [] }

theorem upper_31 : Upper D R [18,257,40,528] 13 :=
  bound_sound D R [18,257,40,528] 13 bound_31
    ((Boolean.boundCheck_true D R [18,257,40,528] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 259 44 552 212 244 212 212 468 724), lower := (rows 19 259 44 552 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [18,257,40,544] 13 :=
  bound_sound D R [18,257,40,544] 13 bound_32
    ((Boolean.boundCheck_true D R [18,257,40,544] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 19 259 44 584 244 244 244 244 500 756), lower := (rows 19 259 44 584 16 32 64 128 256 512), losses := [] }

theorem upper_33 : Upper D R [18,257,40,576] 13 :=
  bound_sound D R [18,257,40,576] 13 bound_33
    ((Boolean.boundCheck_true D R [18,257,40,576] 13 bound_33).mp (by decide +kernel))

def route_6 : Route 10 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_6 : Upper D R [18,257,40] 13 := by
  apply routed_branch D R [18,257,40] 13 (by decide) (choices 2) [20,36,48,68,80,96,192,516,528,544,576] route_6
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,257,40] (choices 2) [20,36,48,68,80,96,192,516,528,544,576] route_6).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_7
  · exact upper_8
  · exact upper_9
  · exact upper_10
  · exact upper_11
  · exact upper_12
  · exact upper_13
  · exact upper_14
  · exact upper_31
  · exact upper_32
  · exact upper_33

def bound_34 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 19 259 52 748 764 748 748 748 1004 748), lower := (rows 19 259 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_34 : Upper D R [18,257,48] 13 :=
  bound_sound D R [18,257,48] 13 bound_34
    ((Boolean.boundCheck_true D R [18,257,48] 13 bound_34).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 224 240 144 240 0 0 0 0 0 0), upper := (rows 19 259 100 764 764 764 764 764 1020 764), lower := (rows 19 259 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_35 : Upper D R [18,257,96] 13 :=
  bound_sound D R [18,257,96] 13 bound_35
    ((Boolean.boundCheck_true D R [18,257,96] 13 bound_35).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 19 259 524 28 240 224 224 224 480 736), lower := (rows 19 259 524 28 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 3 12 8 0 1023 1023 1023 1023 1023), good := (rows 995 995 1004 1004 992 992 992 992 992 992) }] }

theorem upper_37 : Upper D R [18,257,520,20] 13 :=
  bound_sound D R [18,257,520,20] 13 bound_37
    ((Boolean.boundCheck_true D R [18,257,520,20] 13 bound_37).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 192 208 240 208 0 0 0 0 0 0), upper := (rows 19 259 524 44 48 240 208 208 464 720), lower := (rows 19 259 524 44 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 17 19 4 8 16 0 81 145 273 529), good := (rows 979 963 524 12 979 0 64 128 256 512) }] }

theorem upper_39 : Upper D R [18,257,520,36,32] 13 :=
  bound_sound D R [18,257,520,36,32] 13 bound_39
    ((Boolean.boundCheck_true D R [18,257,520,36,32] 13 bound_39).mp (by decide +kernel))

def bound_41 : Bound 10 := { allowed := (rows 224 240 224 192 0 0 0 0 0 0), upper := (rows 19 259 524 44 80 48 224 224 480 736), lower := (rows 19 259 524 44 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 44 40 0 32 104 168 296 552), good := (rows 3 259 972 1004 64 1004 64 128 256 512) }] }

theorem upper_41 : Upper D R [18,257,520,36,64,16] 13 :=
  bound_sound D R [18,257,520,36,64,16] 13 bound_41
    ((Boolean.boundCheck_true D R [18,257,520,36,64,16] 13 bound_41).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 19 259 524 44 80 96 80 160 416 672), lower := (rows 19 259 524 44 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 127 121 0 112 64 249 377 633), good := (rows 943 911 908 940 1004 1004 1004 128 256 512) }] }

theorem upper_43 : Upper D R [18,257,520,36,64,64,16] 13 :=
  bound_sound D R [18,257,520,36,64,64,16] 13 bound_43
    ((Boolean.boundCheck_true D R [18,257,520,36,64,64,16] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 224 240 224 192 0 0 0 0 0 0), upper := (rows 19 259 524 44 80 96 96 144 400 656), lower := (rows 19 259 524 44 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 516 524 0 1023 1023 128 256 512), good := (rows 99 355 620 108 96 96 96 224 352 620) }] }

theorem upper_44 : Upper D R [18,257,520,36,64,64,32] 13 :=
  bound_sound D R [18,257,520,36,64,64,32] 13 bound_44
    ((Boolean.boundCheck_true D R [18,257,520,36,64,64,32] 13 bound_44).mp (by decide +kernel))

def bound_46 : Bound 10 := { allowed := (rows 224 240 224 192 0 0 0 0 0 0), upper := (rows 19 259 524 44 80 96 192 144 416 672), lower := (rows 19 259 524 44 80 96 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 244 249 0 240 192 128 448 704), good := (rows 47 267 524 44 876 876 1004 1004 256 512) }] }

theorem upper_46 : Upper D R [18,257,520,36,64,64,128,16] 13 :=
  bound_sound D R [18,257,520,36,64,64,128,16] 13 bound_46
    ((Boolean.boundCheck_true D R [18,257,520,36,64,64,128,16] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 224 240 224 192 0 0 0 0 0 0), upper := (rows 19 259 524 44 80 96 192 160 400 656), lower := (rows 19 259 524 44 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 516 524 0 1023 1023 1023 256 512), good := (rows 227 483 748 236 224 224 224 224 480 748) }] }

theorem upper_47 : Upper D R [18,257,520,36,64,64,128,32] 13 :=
  bound_sound D R [18,257,520,36,64,64,128,32] 13 bound_47
    ((Boolean.boundCheck_true D R [18,257,520,36,64,64,128,32] 13 bound_47).mp (by decide +kernel))

def route_45 : Route 10 := (fun mask => (mask,id))

theorem upper_45 : Upper D R [18,257,520,36,64,64,128] 13 := by
  apply routed_branch D R [18,257,520,36,64,64,128] 13 (by decide) (choices 1) [16,32] route_45
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,257,520,36,64,64,128] (choices 1) [16,32] route_45).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_46
  · exact upper_47

def route_42 : Route 10 := (fun mask => (mask,id))

theorem upper_42 : Upper D R [18,257,520,36,64,64] 13 := by
  apply routed_branch D R [18,257,520,36,64,64] 13 (by decide) (choices 1) [16,32,128] route_42
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,257,520,36,64,64] (choices 1) [16,32,128] route_42).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_43
  · exact upper_44
  · exact upper_45

def bound_49 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 19 259 524 44 80 160 80 224 480 736), lower := (rows 19 259 524 44 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 85 91 0 241 64 208 336 592), good := (rows 943 303 524 44 1004 160 1004 160 256 512) }] }

theorem upper_49 : Upper D R [18,257,520,36,64,128,16] 13 :=
  bound_sound D R [18,257,520,36,64,128,16] 13 bound_49
    ((Boolean.boundCheck_true D R [18,257,520,36,64,128,16] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 192 208 240 208 0 0 0 0 0 0), upper := (rows 19 259 524 44 80 160 96 208 464 720), lower := (rows 19 259 524 44 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 81 83 4 8 80 0 64 208 336 592), good := (rows 915 259 524 12 979 128 979 128 256 512) }] }

theorem upper_50 : Upper D R [18,257,520,36,64,128,32] 13 :=
  bound_sound D R [18,257,520,36,64,128,32] 13 bound_50
    ((Boolean.boundCheck_true D R [18,257,520,36,64,128,32] 13 bound_50).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 19 259 524 44 80 160 192 144 352 608), lower := (rows 19 259 524 44 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 3 253 248 0 224 224 128 504 760), good := (rows 783 263 780 876 876 1004 1004 1004 256 512) }] }

theorem upper_52 : Upper D R [18,257,520,36,64,128,128,16] 13 :=
  bound_sound D R [18,257,520,36,64,128,128,16] 13 bound_52
    ((Boolean.boundCheck_true D R [18,257,520,36,64,128,128,16] 13 bound_52).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 224 240 224 192 0 0 0 0 0 0), upper := (rows 19 259 524 44 80 160 192 160 336 592), lower := (rows 19 259 524 44 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 516 524 0 1023 1023 1023 256 512), good := (rows 227 483 748 236 224 224 224 224 480 748) }] }

theorem upper_53 : Upper D R [18,257,520,36,64,128,128,32] 13 :=
  bound_sound D R [18,257,520,36,64,128,128,32] 13 bound_53
    ((Boolean.boundCheck_true D R [18,257,520,36,64,128,128,32] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 224 240 224 192 0 0 0 0 0 0), upper := (rows 19 259 524 44 80 160 192 192 304 560), lower := (rows 19 259 524 44 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 516 524 0 1023 1023 1023 256 512), good := (rows 227 483 748 236 224 224 224 224 480 748) }] }

theorem upper_54 : Upper D R [18,257,520,36,64,128,128,64] 13 :=
  bound_sound D R [18,257,520,36,64,128,128,64] 13 bound_54
    ((Boolean.boundCheck_true D R [18,257,520,36,64,128,128,64] 13 bound_54).mp (by decide +kernel))

def route_51 : Route 10 := (fun mask => (mask,id))

theorem upper_51 : Upper D R [18,257,520,36,64,128,128] 13 := by
  apply routed_branch D R [18,257,520,36,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_51
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,257,520,36,64,128,128] (choices 1) [16,32,64] route_51).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_52
  · exact upper_53
  · exact upper_54

def route_48 : Route 10 := (fun mask => (mask,id))

theorem upper_48 : Upper D R [18,257,520,36,64,128] 13 := by
  apply routed_branch D R [18,257,520,36,64,128] 13 (by decide) (choices 1) [16,32,128] route_48
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,257,520,36,64,128] (choices 1) [16,32,128] route_48).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_49
  · exact upper_50
  · exact upper_51

def route_40 : Route 10 := (fun mask => (mask,id))

theorem upper_40 : Upper D R [18,257,520,36,64] 13 := by
  apply routed_branch D R [18,257,520,36,64] 13 (by decide) (choices 1) [16,64,128] route_40
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,257,520,36,64] (choices 1) [16,64,128] route_40).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_41
  · exact upper_42
  · exact upper_48

def route_38 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_38 : Upper D R [18,257,520,36] 13 := by
  apply routed_branch D R [18,257,520,36] 13 (by decide) (choices 1) [32,64] route_38
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,257,520,36] (choices 1) [32,64] route_38).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_39
  · exact upper_40

def bound_55 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 19 259 524 56 244 228 228 228 484 740), lower := (rows 19 259 524 56 16 32 64 128 256 512), losses := [] }

theorem upper_55 : Upper D R [18,257,520,48] 13 :=
  bound_sound D R [18,257,520,48] 13 bound_55
    ((Boolean.boundCheck_true D R [18,257,520,48] 13 bound_55).mp (by decide +kernel))

def bound_56 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 19 259 524 104 244 244 244 244 500 756), lower := (rows 19 259 524 104 16 32 64 128 256 512), losses := [] }

theorem upper_56 : Upper D R [18,257,520,96] 13 :=
  bound_sound D R [18,257,520,96] 13 bound_56
    ((Boolean.boundCheck_true D R [18,257,520,96] 13 bound_56).mp (by decide +kernel))

def route_36 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_36 : Upper D R [18,257,520] 13 := by
  apply routed_branch D R [18,257,520] 13 (by decide) (choices 2) [20,36,48,96] route_36
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,257,520] (choices 2) [20,36,48,96] route_36).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_37
  · exact upper_38
  · exact upper_55
  · exact upper_56

def bound_58 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 19 259 532 44 248 232 232 232 488 744), lower := (rows 19 259 532 44 16 32 64 128 256 512), losses := [] }

theorem upper_58 : Upper D R [18,257,528,36] 13 :=
  bound_sound D R [18,257,528,36] 13 bound_58
    ((Boolean.boundCheck_true D R [18,257,528,36] 13 bound_58).mp (by decide +kernel))

def bound_59 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 19 259 532 104 252 236 236 236 492 748), lower := (rows 19 259 532 104 16 32 64 128 256 512), losses := [] }

theorem upper_59 : Upper D R [18,257,528,96] 13 :=
  bound_sound D R [18,257,528,96] 13 bound_59
    ((Boolean.boundCheck_true D R [18,257,528,96] 13 bound_59).mp (by decide +kernel))

def route_57 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_57 : Upper D R [18,257,528] 13 := by
  apply routed_branch D R [18,257,528] 13 (by decide) (choices 2) [36,96] route_57
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,257,528] (choices 2) [36,96] route_57).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_58
  · exact upper_59

def bound_61 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 19 259 548 28 248 232 232 232 488 744), lower := (rows 19 259 548 28 16 32 64 128 256 512), losses := [] }

theorem upper_61 : Upper D R [18,257,544,20] 13 :=
  bound_sound D R [18,257,544,20] 13 bound_61
    ((Boolean.boundCheck_true D R [18,257,544,20] 13 bound_61).mp (by decide +kernel))

def bound_62 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 259 548 44 216 248 216 216 472 728), lower := (rows 19 259 548 44 16 32 64 128 256 512), losses := [] }

theorem upper_62 : Upper D R [18,257,544,36] 13 :=
  bound_sound D R [18,257,544,36] 13 bound_62
    ((Boolean.boundCheck_true D R [18,257,544,36] 13 bound_62).mp (by decide +kernel))

def bound_63 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 19 259 548 56 220 236 204 204 460 716), lower := (rows 19 259 548 56 16 32 64 128 256 512), losses := [] }

theorem upper_63 : Upper D R [18,257,544,48] 13 :=
  bound_sound D R [18,257,544,48] 13 bound_63
    ((Boolean.boundCheck_true D R [18,257,544,48] 13 bound_63).mp (by decide +kernel))

def bound_64 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 19 259 548 76 248 248 248 248 504 760), lower := (rows 19 259 548 76 16 32 64 128 256 512), losses := [] }

theorem upper_64 : Upper D R [18,257,544,68] 13 :=
  bound_sound D R [18,257,544,68] 13 bound_64
    ((Boolean.boundCheck_true D R [18,257,544,68] 13 bound_64).mp (by decide +kernel))

def bound_65 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 19 259 548 88 252 236 236 236 492 748), lower := (rows 19 259 548 88 16 32 64 128 256 512), losses := [] }

theorem upper_65 : Upper D R [18,257,544,80] 13 :=
  bound_sound D R [18,257,544,80] 13 bound_65
    ((Boolean.boundCheck_true D R [18,257,544,80] 13 bound_65).mp (by decide +kernel))

def bound_66 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 19 259 548 104 220 252 220 220 476 732), lower := (rows 19 259 548 104 16 32 64 128 256 512), losses := [] }

theorem upper_66 : Upper D R [18,257,544,96] 13 :=
  bound_sound D R [18,257,544,96] 13 bound_66
    ((Boolean.boundCheck_true D R [18,257,544,96] 13 bound_66).mp (by decide +kernel))

def bound_67 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 19 259 548 200 252 252 252 252 508 764), lower := (rows 19 259 548 200 16 32 64 128 256 512), losses := [] }

theorem upper_67 : Upper D R [18,257,544,192] 13 :=
  bound_sound D R [18,257,544,192] 13 bound_67
    ((Boolean.boundCheck_true D R [18,257,544,192] 13 bound_67).mp (by decide +kernel))

def route_60 : Route 10 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_60 : Upper D R [18,257,544] 13 := by
  apply routed_branch D R [18,257,544] 13 (by decide) (choices 2) [20,36,48,68,80,96,192] route_60
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,257,544] (choices 2) [20,36,48,68,80,96,192] route_60).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_61
  · exact upper_62
  · exact upper_63
  · exact upper_64
  · exact upper_65
  · exact upper_66
  · exact upper_67

def route_0 : Route 10 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [18,257] 13 := by
  apply routed_branch D R [18,257] 13 (by decide) (choices 2) [24,40,48,96,520,528,544] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,257] (choices 2) [24,40,48,96,520,528,544] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_6
  · exact upper_34
  · exact upper_35
  · exact upper_36
  · exact upper_57
  · exact upper_60

theorem upper : Upper D R [18,257] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case16
