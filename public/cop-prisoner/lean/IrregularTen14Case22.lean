import IrregularTen14Base

namespace Delivery.IrregularTen14.Case22
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 14 7 56 976 992 960 960 960 960), lower := (rows 49 14 7 56 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [48,12,3,48] 13 :=
  bound_sound D R [48,12,3,48] 13 bound_2
    ((Boolean.boundCheck_true D R [48,12,3,48] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 14 7 88 1008 992 992 992 992 992), lower := (rows 49 14 7 88 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [48,12,3,80] 13 :=
  bound_sound D R [48,12,3,80] 13 bound_3
    ((Boolean.boundCheck_true D R [48,12,3,80] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 14 7 200 1008 1008 1008 1008 1008 1008), lower := (rows 49 14 7 200 16 32 64 128 256 512), losses := [] }

theorem upper_4 : Upper D R [48,12,3,192] 13 :=
  bound_sound D R [48,12,3,192] 13 bound_4
    ((Boolean.boundCheck_true D R [48,12,3,192] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 14 7 280 752 736 736 736 992 736), lower := (rows 49 14 7 280 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [48,12,3,272] 13 :=
  bound_sound D R [48,12,3,272] 13 bound_5
    ((Boolean.boundCheck_true D R [48,12,3,272] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 14 7 328 752 752 752 752 1008 752), lower := (rows 49 14 7 328 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [48,12,3,320] 13 :=
  bound_sound D R [48,12,3,320] 13 bound_6
    ((Boolean.boundCheck_true D R [48,12,3,320] 13 bound_6).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 14 7 776 48 240 208 208 464 720), lower := (rows 49 14 7 776 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 7 5 29 16 0 81 145 273 529), good := (rows 991 14 975 776 984 0 64 128 256 512) }] }

theorem upper_8 : Upper D R [48,12,3,768,32] 13 :=
  bound_sound D R [48,12,3,768,32] 13 bound_8
    ((Boolean.boundCheck_true D R [48,12,3,768,32] 13 bound_8).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 14 7 776 80 48 224 224 480 736), lower := (rows 49 14 7 776 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 45 0 32 97 161 289 545), good := (rows 1007 14 975 776 64 1000 64 128 256 512) }] }

theorem upper_10 : Upper D R [48,12,3,768,64,16] 13 :=
  bound_sound D R [48,12,3,768,64,16] 13 bound_10
    ((Boolean.boundCheck_true D R [48,12,3,768,64,16] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 192 176 176 176 0 0 0 0 0 0), upper := (rows 49 14 7 776 80 96 240 176 432 688), lower := (rows 49 14 7 776 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 1 7 5 13 16 32 0 129 257 513), good := (rows 959 14 911 776 16 32 0 128 256 512) }] }

theorem upper_11 : Upper D R [48,12,3,768,64,64] 13 :=
  bound_sound D R [48,12,3,768,64,64] 13 bound_11
    ((Boolean.boundCheck_true D R [48,12,3,768,64,64] 13 bound_11).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 14 7 776 80 160 80 224 480 736), lower := (rows 49 14 7 776 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 89 0 241 64 208 336 592), good := (rows 943 14 47 776 1000 160 1000 160 256 512) }] }

theorem upper_13 : Upper D R [48,12,3,768,64,128,16] 13 :=
  bound_sound D R [48,12,3,768,64,128,16] 13 bound_13
    ((Boolean.boundCheck_true D R [48,12,3,768,64,128,16] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 14 7 776 80 160 96 208 464 720), lower := (rows 49 14 7 776 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 7 5 89 80 0 64 208 336 592), good := (rows 927 14 15 776 984 128 984 128 256 512) }] }

theorem upper_14 : Upper D R [48,12,3,768,64,128,32] 13 :=
  bound_sound D R [48,12,3,768,64,128,32] 13 bound_14
    ((Boolean.boundCheck_true D R [48,12,3,768,64,128,32] 13 bound_14).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 128 240 240 240 0 0 0 0 0 0), upper := (rows 49 14 7 776 80 160 192 240 368 624), lower := (rows 49 14 7 776 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 17 2 4 8 16 224 0 128 256 512), good := (rows 49 14 7 776 49 160 160 160 256 512) }] }

theorem upper_15 : Upper D R [48,12,3,768,64,128,128] 13 :=
  bound_sound D R [48,12,3,768,64,128,128] 13 bound_15
    ((Boolean.boundCheck_true D R [48,12,3,768,64,128,128] 13 bound_15).mp (by decide +kernel))

def route_12 : Route 10 := (fun mask => (mask,id))

theorem upper_12 : Upper D R [48,12,3,768,64,128] 13 := by
  apply routed_branch D R [48,12,3,768,64,128] 13 (by decide) (choices 1) [16,32,128] route_12
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,12,3,768,64,128] (choices 1) [16,32,128] route_12).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_13
  · exact upper_14
  · exact upper_15

def route_9 : Route 10 := (fun mask => (mask,id))

theorem upper_9 : Upper D R [48,12,3,768,64] 13 := by
  apply routed_branch D R [48,12,3,768,64] 13 (by decide) (choices 1) [16,64,128] route_9
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,12,3,768,64] (choices 1) [16,64,128] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_10
  · exact upper_11
  · exact upper_12

def route_7 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_7 : Upper D R [48,12,3,768] 13 := by
  apply routed_branch D R [48,12,3,768] 13 (by decide) (choices 1) [32,64] route_7
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,12,3,768] (choices 1) [32,64] route_7).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_8
  · exact upper_9

def route_1 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 544 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [48,12,3] 13 := by
  apply routed_branch D R [48,12,3] 13 (by decide) (choices 2) [48,80,192,272,320,768] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,12,3] (choices 2) [48,80,192,272,320,768] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5
  · exact upper_6
  · exact upper_7

def bound_16 : Bound 10 := { allowed := (rows 192 240 224 240 0 0 0 0 0 0), upper := (rows 49 14 21 1002 1010 994 994 994 994 994), lower := (rows 49 14 21 8 16 32 64 128 256 512), losses := [] }

theorem upper_16 : Upper D R [48,12,17] 13 :=
  bound_sound D R [48,12,17] 13 bound_16
    ((Boolean.boundCheck_true D R [48,12,17] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 192 240 224 240 0 0 0 0 0 0), upper := (rows 49 14 22 1001 1009 993 993 993 993 993), lower := (rows 49 14 22 8 16 32 64 128 256 512), losses := [] }

theorem upper_17 : Upper D R [48,12,18] 13 :=
  bound_sound D R [48,12,18] 13 bound_17
    ((Boolean.boundCheck_true D R [48,12,18] 13 bound_17).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 192 240 192 240 0 0 0 0 0 0), upper := (rows 49 14 52 971 979 995 963 963 963 963), lower := (rows 49 14 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_18 : Upper D R [48,12,48] 13 :=
  bound_sound D R [48,12,48] 13 bound_18
    ((Boolean.boundCheck_true D R [48,12,48] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 192 240 176 240 0 0 0 0 0 0), upper := (rows 49 14 69 1018 1010 1010 1010 1010 1010 1010), lower := (rows 49 14 69 8 16 32 64 128 256 512), losses := [] }

theorem upper_19 : Upper D R [48,12,65] 13 :=
  bound_sound D R [48,12,65] 13 bound_19
    ((Boolean.boundCheck_true D R [48,12,65] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 192 240 176 240 0 0 0 0 0 0), upper := (rows 49 14 70 1017 1009 1009 1009 1009 1009 1009), lower := (rows 49 14 70 8 16 32 64 128 256 512), losses := [] }

theorem upper_20 : Upper D R [48,12,66] 13 :=
  bound_sound D R [48,12,66] 13 bound_20
    ((Boolean.boundCheck_true D R [48,12,66] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 192 240 160 240 0 0 0 0 0 0), upper := (rows 49 14 84 1003 1011 995 995 995 995 995), lower := (rows 49 14 84 8 16 32 64 128 256 512), losses := [] }

theorem upper_21 : Upper D R [48,12,80] 13 :=
  bound_sound D R [48,12,80] 13 bound_21
    ((Boolean.boundCheck_true D R [48,12,80] 13 bound_21).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 192 240 48 240 0 0 0 0 0 0), upper := (rows 49 14 196 1019 1011 1011 1011 1011 1011 1011), lower := (rows 49 14 196 8 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [48,12,192] 13 :=
  bound_sound D R [48,12,192] 13 bound_22
    ((Boolean.boundCheck_true D R [48,12,192] 13 bound_22).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 14 261 26 752 736 736 736 992 736), lower := (rows 49 14 261 26 16 32 64 128 256 512), losses := [] }

theorem upper_24 : Upper D R [48,12,257,18] 13 :=
  bound_sound D R [48,12,257,18] 13 bound_24
    ((Boolean.boundCheck_true D R [48,12,257,18] 13 bound_24).mp (by decide +kernel))

def bound_25 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 14 261 56 722 738 706 706 962 706), lower := (rows 49 14 261 56 16 32 64 128 256 512), losses := [] }

theorem upper_25 : Upper D R [48,12,257,48] 13 :=
  bound_sound D R [48,12,257,48] 13 bound_25
    ((Boolean.boundCheck_true D R [48,12,257,48] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 14 261 74 752 752 752 752 1008 752), lower := (rows 49 14 261 74 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [48,12,257,66] 13 :=
  bound_sound D R [48,12,257,66] 13 bound_26
    ((Boolean.boundCheck_true D R [48,12,257,66] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 14 261 88 754 738 738 738 994 738), lower := (rows 49 14 261 88 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [48,12,257,80] 13 :=
  bound_sound D R [48,12,257,80] 13 bound_27
    ((Boolean.boundCheck_true D R [48,12,257,80] 13 bound_27).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 14 261 200 754 754 754 754 1010 754), lower := (rows 49 14 261 200 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [48,12,257,192] 13 :=
  bound_sound D R [48,12,257,192] 13 bound_28
    ((Boolean.boundCheck_true D R [48,12,257,192] 13 bound_28).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 14 261 522 48 240 208 208 464 720), lower := (rows 49 14 261 522 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 7 5 13 16 0 81 145 273 529), good := (rows 991 14 975 522 976 0 64 128 256 512) }] }

theorem upper_30 : Upper D R [48,12,257,514,32] 13 :=
  bound_sound D R [48,12,257,514,32] 13 bound_30
    ((Boolean.boundCheck_true D R [48,12,257,514,32] 13 bound_30).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 14 261 522 80 48 224 224 480 736), lower := (rows 49 14 261 522 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 13 0 32 97 161 289 545), good := (rows 1007 14 975 522 64 992 64 128 256 512) }] }

theorem upper_32 : Upper D R [48,12,257,514,64,16] 13 :=
  bound_sound D R [48,12,257,514,64,16] 13 bound_32
    ((Boolean.boundCheck_true D R [48,12,257,514,64,16] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 192 176 176 176 0 0 0 0 0 0), upper := (rows 49 14 261 522 80 96 240 176 432 688), lower := (rows 49 14 261 522 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 1 7 5 13 16 32 0 129 257 513), good := (rows 959 14 911 522 16 32 0 128 256 512) }] }

theorem upper_33 : Upper D R [48,12,257,514,64,64] 13 :=
  bound_sound D R [48,12,257,514,64,64] 13 bound_33
    ((Boolean.boundCheck_true D R [48,12,257,514,64,64] 13 bound_33).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 14 261 522 80 160 80 224 480 736), lower := (rows 49 14 261 522 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 9 0 241 64 208 336 592), good := (rows 943 14 303 522 992 160 992 160 256 512) }] }

theorem upper_35 : Upper D R [48,12,257,514,64,128,16] 13 :=
  bound_sound D R [48,12,257,514,64,128,16] 13 bound_35
    ((Boolean.boundCheck_true D R [48,12,257,514,64,128,16] 13 bound_35).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 14 261 522 80 160 96 208 464 720), lower := (rows 49 14 261 522 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 7 5 9 80 0 64 208 336 592), good := (rows 927 14 271 522 976 128 976 128 256 512) }] }

theorem upper_36 : Upper D R [48,12,257,514,64,128,32] 13 :=
  bound_sound D R [48,12,257,514,64,128,32] 13 bound_36
    ((Boolean.boundCheck_true D R [48,12,257,514,64,128,32] 13 bound_36).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 128 240 240 240 0 0 0 0 0 0), upper := (rows 49 14 261 522 80 160 192 240 368 624), lower := (rows 49 14 261 522 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 17 2 4 8 16 224 0 128 256 512), good := (rows 49 14 261 522 49 160 160 160 256 512) }] }

theorem upper_37 : Upper D R [48,12,257,514,64,128,128] 13 :=
  bound_sound D R [48,12,257,514,64,128,128] 13 bound_37
    ((Boolean.boundCheck_true D R [48,12,257,514,64,128,128] 13 bound_37).mp (by decide +kernel))

def route_34 : Route 10 := (fun mask => (mask,id))

theorem upper_34 : Upper D R [48,12,257,514,64,128] 13 := by
  apply routed_branch D R [48,12,257,514,64,128] 13 (by decide) (choices 1) [16,32,128] route_34
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,12,257,514,64,128] (choices 1) [16,32,128] route_34).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_35
  · exact upper_36
  · exact upper_37

def route_31 : Route 10 := (fun mask => (mask,id))

theorem upper_31 : Upper D R [48,12,257,514,64] 13 := by
  apply routed_branch D R [48,12,257,514,64] 13 (by decide) (choices 1) [16,64,128] route_31
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,12,257,514,64] (choices 1) [16,64,128] route_31).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_32
  · exact upper_33
  · exact upper_34

def route_29 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_29 : Upper D R [48,12,257,514] 13 := by
  apply routed_branch D R [48,12,257,514] 13 (by decide) (choices 1) [32,64] route_29
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,12,257,514] (choices 1) [32,64] route_29).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_30
  · exact upper_31

def bound_38 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 14 261 536 242 226 226 226 482 738), lower := (rows 49 14 261 536 16 32 64 128 256 512), losses := [] }

theorem upper_38 : Upper D R [48,12,257,528] 13 :=
  bound_sound D R [48,12,257,528] 13 bound_38
    ((Boolean.boundCheck_true D R [48,12,257,528] 13 bound_38).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 14 261 584 242 242 242 242 498 754), lower := (rows 49 14 261 584 16 32 64 128 256 512), losses := [] }

theorem upper_39 : Upper D R [48,12,257,576] 13 :=
  bound_sound D R [48,12,257,576] 13 bound_39
    ((Boolean.boundCheck_true D R [48,12,257,576] 13 bound_39).mp (by decide +kernel))

def route_23 : Route 10 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_23 : Upper D R [48,12,257] 13 := by
  apply routed_branch D R [48,12,257] 13 (by decide) (choices 2) [18,48,66,80,192,514,528,576] route_23
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,12,257] (choices 2) [18,48,66,80,192,514,528,576] route_23).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_24
  · exact upper_25
  · exact upper_26
  · exact upper_27
  · exact upper_28
  · exact upper_29
  · exact upper_38
  · exact upper_39

def bound_41 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 14 262 25 752 736 736 736 992 736), lower := (rows 49 14 262 25 16 32 64 128 256 512), losses := [] }

theorem upper_41 : Upper D R [48,12,258,17] 13 :=
  bound_sound D R [48,12,258,17] 13 bound_41
    ((Boolean.boundCheck_true D R [48,12,258,17] 13 bound_41).mp (by decide +kernel))

def bound_42 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 14 262 56 721 737 705 705 961 705), lower := (rows 49 14 262 56 16 32 64 128 256 512), losses := [] }

theorem upper_42 : Upper D R [48,12,258,48] 13 :=
  bound_sound D R [48,12,258,48] 13 bound_42
    ((Boolean.boundCheck_true D R [48,12,258,48] 13 bound_42).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 14 262 73 752 752 752 752 1008 752), lower := (rows 49 14 262 73 16 32 64 128 256 512), losses := [] }

theorem upper_43 : Upper D R [48,12,258,65] 13 :=
  bound_sound D R [48,12,258,65] 13 bound_43
    ((Boolean.boundCheck_true D R [48,12,258,65] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 14 262 88 753 737 737 737 993 737), lower := (rows 49 14 262 88 16 32 64 128 256 512), losses := [] }

theorem upper_44 : Upper D R [48,12,258,80] 13 :=
  bound_sound D R [48,12,258,80] 13 bound_44
    ((Boolean.boundCheck_true D R [48,12,258,80] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 14 262 200 753 753 753 753 1009 753), lower := (rows 49 14 262 200 16 32 64 128 256 512), losses := [] }

theorem upper_45 : Upper D R [48,12,258,192] 13 :=
  bound_sound D R [48,12,258,192] 13 bound_45
    ((Boolean.boundCheck_true D R [48,12,258,192] 13 bound_45).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 14 262 521 48 240 208 208 464 720), lower := (rows 49 14 262 521 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 11 13 9 16 0 81 145 273 529), good := (rows 991 14 262 975 976 0 64 128 256 512) }] }

theorem upper_47 : Upper D R [48,12,258,513,32] 13 :=
  bound_sound D R [48,12,258,513,32] 13 bound_47
    ((Boolean.boundCheck_true D R [48,12,258,513,32] 13 bound_47).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 14 262 521 80 48 224 224 480 736), lower := (rows 49 14 262 521 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 11 13 9 0 32 97 161 289 545), good := (rows 1007 14 262 975 64 992 64 128 256 512) }] }

theorem upper_49 : Upper D R [48,12,258,513,64,16] 13 :=
  bound_sound D R [48,12,258,513,64,16] 13 bound_49
    ((Boolean.boundCheck_true D R [48,12,258,513,64,16] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 192 176 176 176 0 0 0 0 0 0), upper := (rows 49 14 262 521 80 96 240 176 432 688), lower := (rows 49 14 262 521 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 1 11 13 9 16 32 0 129 257 513), good := (rows 959 14 262 911 16 32 0 128 256 512) }] }

theorem upper_50 : Upper D R [48,12,258,513,64,64] 13 :=
  bound_sound D R [48,12,258,513,64,64] 13 bound_50
    ((Boolean.boundCheck_true D R [48,12,258,513,64,64] 13 bound_50).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 14 262 521 80 160 80 224 480 736), lower := (rows 49 14 262 521 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 11 5 9 0 241 64 208 336 592), good := (rows 943 14 262 559 992 160 992 160 256 512) }] }

theorem upper_52 : Upper D R [48,12,258,513,64,128,16] 13 :=
  bound_sound D R [48,12,258,513,64,128,16] 13 bound_52
    ((Boolean.boundCheck_true D R [48,12,258,513,64,128,16] 13 bound_52).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 14 262 521 80 160 96 208 464 720), lower := (rows 49 14 262 521 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 11 5 9 80 0 64 208 336 592), good := (rows 927 14 262 527 976 128 976 128 256 512) }] }

theorem upper_53 : Upper D R [48,12,258,513,64,128,32] 13 :=
  bound_sound D R [48,12,258,513,64,128,32] 13 bound_53
    ((Boolean.boundCheck_true D R [48,12,258,513,64,128,32] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 128 240 240 240 0 0 0 0 0 0), upper := (rows 49 14 262 521 80 160 192 240 368 624), lower := (rows 49 14 262 521 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 17 2 4 8 16 224 0 128 256 512), good := (rows 49 14 262 521 49 160 160 160 256 512) }] }

theorem upper_54 : Upper D R [48,12,258,513,64,128,128] 13 :=
  bound_sound D R [48,12,258,513,64,128,128] 13 bound_54
    ((Boolean.boundCheck_true D R [48,12,258,513,64,128,128] 13 bound_54).mp (by decide +kernel))

def route_51 : Route 10 := (fun mask => (mask,id))

theorem upper_51 : Upper D R [48,12,258,513,64,128] 13 := by
  apply routed_branch D R [48,12,258,513,64,128] 13 (by decide) (choices 1) [16,32,128] route_51
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,12,258,513,64,128] (choices 1) [16,32,128] route_51).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_52
  · exact upper_53
  · exact upper_54

def route_48 : Route 10 := (fun mask => (mask,id))

theorem upper_48 : Upper D R [48,12,258,513,64] 13 := by
  apply routed_branch D R [48,12,258,513,64] 13 (by decide) (choices 1) [16,64,128] route_48
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,12,258,513,64] (choices 1) [16,64,128] route_48).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_49
  · exact upper_50
  · exact upper_51

def route_46 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_46 : Upper D R [48,12,258,513] 13 := by
  apply routed_branch D R [48,12,258,513] 13 (by decide) (choices 1) [32,64] route_46
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,12,258,513] (choices 1) [32,64] route_46).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_47
  · exact upper_48

def bound_55 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 14 262 536 241 225 225 225 481 737), lower := (rows 49 14 262 536 16 32 64 128 256 512), losses := [] }

theorem upper_55 : Upper D R [48,12,258,528] 13 :=
  bound_sound D R [48,12,258,528] 13 bound_55
    ((Boolean.boundCheck_true D R [48,12,258,528] 13 bound_55).mp (by decide +kernel))

def bound_56 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 14 262 584 241 241 241 241 497 753), lower := (rows 49 14 262 584 16 32 64 128 256 512), losses := [] }

theorem upper_56 : Upper D R [48,12,258,576] 13 :=
  bound_sound D R [48,12,258,576] 13 bound_56
    ((Boolean.boundCheck_true D R [48,12,258,576] 13 bound_56).mp (by decide +kernel))

def route_40 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_40 : Upper D R [48,12,258] 13 := by
  apply routed_branch D R [48,12,258] 13 (by decide) (choices 2) [17,48,65,80,192,513,528,576] route_40
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,12,258] (choices 2) [17,48,65,80,192,513,528,576] route_40).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_41
  · exact upper_42
  · exact upper_43
  · exact upper_44
  · exact upper_45
  · exact upper_46
  · exact upper_55
  · exact upper_56

def bound_57 : Bound 10 := { allowed := (rows 192 240 224 240 0 0 0 0 0 0), upper := (rows 49 14 276 747 755 739 739 739 995 739), lower := (rows 49 14 276 8 16 32 64 128 256 512), losses := [] }

theorem upper_57 : Upper D R [48,12,272] 13 :=
  bound_sound D R [48,12,272] 13 bound_57
    ((Boolean.boundCheck_true D R [48,12,272] 13 bound_57).mp (by decide +kernel))

def bound_58 : Bound 10 := { allowed := (rows 192 240 176 240 0 0 0 0 0 0), upper := (rows 49 14 324 763 755 755 755 755 1011 755), lower := (rows 49 14 324 8 16 32 64 128 256 512), losses := [] }

theorem upper_58 : Upper D R [48,12,320] 13 :=
  bound_sound D R [48,12,320] 13 bound_58
    ((Boolean.boundCheck_true D R [48,12,320] 13 bound_58).mp (by decide +kernel))

def bound_61 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 14 772 11 48 240 208 208 464 720), lower := (rows 49 14 772 11 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 11 29 9 16 0 81 145 273 529), good := (rows 991 14 772 975 980 0 64 128 256 512) }] }

theorem upper_61 : Upper D R [48,12,768,3,32] 13 :=
  bound_sound D R [48,12,768,3,32] 13 bound_61
    ((Boolean.boundCheck_true D R [48,12,768,3,32] 13 bound_61).mp (by decide +kernel))

def bound_63 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 14 772 11 80 48 224 224 480 736), lower := (rows 49 14 772 11 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 11 45 9 0 32 97 161 289 545), good := (rows 1007 14 772 975 64 996 64 128 256 512) }] }

theorem upper_63 : Upper D R [48,12,768,3,64,16] 13 :=
  bound_sound D R [48,12,768,3,64,16] 13 bound_63
    ((Boolean.boundCheck_true D R [48,12,768,3,64,16] 13 bound_63).mp (by decide +kernel))

def bound_64 : Bound 10 := { allowed := (rows 192 176 176 176 0 0 0 0 0 0), upper := (rows 49 14 772 11 80 96 240 176 432 688), lower := (rows 49 14 772 11 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 1 11 13 9 16 32 0 129 257 513), good := (rows 959 14 772 911 16 32 0 128 256 512) }] }

theorem upper_64 : Upper D R [48,12,768,3,64,64] 13 :=
  bound_sound D R [48,12,768,3,64,64] 13 bound_64
    ((Boolean.boundCheck_true D R [48,12,768,3,64,64] 13 bound_64).mp (by decide +kernel))

def bound_66 : Bound 10 := { allowed := (rows 192 224 224 224 0 0 0 0 0 0), upper := (rows 49 14 772 11 80 160 80 224 480 736), lower := (rows 49 14 772 11 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 11 85 9 0 241 64 208 336 592), good := (rows 943 14 772 47 996 160 996 160 256 512) }] }

theorem upper_66 : Upper D R [48,12,768,3,64,128,16] 13 :=
  bound_sound D R [48,12,768,3,64,128,16] 13 bound_66
    ((Boolean.boundCheck_true D R [48,12,768,3,64,128,16] 13 bound_66).mp (by decide +kernel))

def bound_67 : Bound 10 := { allowed := (rows 192 208 208 208 0 0 0 0 0 0), upper := (rows 49 14 772 11 80 160 96 208 464 720), lower := (rows 49 14 772 11 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 11 85 9 80 0 64 208 336 592), good := (rows 927 14 772 15 980 128 980 128 256 512) }] }

theorem upper_67 : Upper D R [48,12,768,3,64,128,32] 13 :=
  bound_sound D R [48,12,768,3,64,128,32] 13 bound_67
    ((Boolean.boundCheck_true D R [48,12,768,3,64,128,32] 13 bound_67).mp (by decide +kernel))

def bound_68 : Bound 10 := { allowed := (rows 128 240 240 240 0 0 0 0 0 0), upper := (rows 49 14 772 11 80 160 192 240 368 624), lower := (rows 49 14 772 11 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 17 2 4 8 16 224 0 128 256 512), good := (rows 49 14 772 11 49 160 160 160 256 512) }] }

theorem upper_68 : Upper D R [48,12,768,3,64,128,128] 13 :=
  bound_sound D R [48,12,768,3,64,128,128] 13 bound_68
    ((Boolean.boundCheck_true D R [48,12,768,3,64,128,128] 13 bound_68).mp (by decide +kernel))

def route_65 : Route 10 := (fun mask => (mask,id))

theorem upper_65 : Upper D R [48,12,768,3,64,128] 13 := by
  apply routed_branch D R [48,12,768,3,64,128] 13 (by decide) (choices 1) [16,32,128] route_65
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,12,768,3,64,128] (choices 1) [16,32,128] route_65).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_66
  · exact upper_67
  · exact upper_68

def route_62 : Route 10 := (fun mask => (mask,id))

theorem upper_62 : Upper D R [48,12,768,3,64] 13 := by
  apply routed_branch D R [48,12,768,3,64] 13 (by decide) (choices 1) [16,64,128] route_62
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,12,768,3,64] (choices 1) [16,64,128] route_62).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_63
  · exact upper_64
  · exact upper_65

def route_60 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_60 : Upper D R [48,12,768,3] 13 := by
  apply routed_branch D R [48,12,768,3] 13 (by decide) (choices 1) [32,64] route_60
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [48,12,768,3] (choices 1) [32,64] route_60).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_61
  · exact upper_62

def bound_69 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 14 772 25 242 226 226 226 482 738), lower := (rows 49 14 772 25 16 32 64 128 256 512), losses := [] }

theorem upper_69 : Upper D R [48,12,768,17] 13 :=
  bound_sound D R [48,12,768,17] 13 bound_69
    ((Boolean.boundCheck_true D R [48,12,768,17] 13 bound_69).mp (by decide +kernel))

def bound_70 : Bound 10 := { allowed := (rows 192 240 240 224 0 0 0 0 0 0), upper := (rows 49 14 772 26 241 225 225 225 481 737), lower := (rows 49 14 772 26 16 32 64 128 256 512), losses := [] }

theorem upper_70 : Upper D R [48,12,768,18] 13 :=
  bound_sound D R [48,12,768,18] 13 bound_70
    ((Boolean.boundCheck_true D R [48,12,768,18] 13 bound_70).mp (by decide +kernel))

def bound_71 : Bound 10 := { allowed := (rows 192 240 240 192 0 0 0 0 0 0), upper := (rows 49 14 772 56 211 227 195 195 451 707), lower := (rows 49 14 772 56 16 32 64 128 256 512), losses := [] }

theorem upper_71 : Upper D R [48,12,768,48] 13 :=
  bound_sound D R [48,12,768,48] 13 bound_71
    ((Boolean.boundCheck_true D R [48,12,768,48] 13 bound_71).mp (by decide +kernel))

def bound_72 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 14 772 73 242 242 242 242 498 754), lower := (rows 49 14 772 73 16 32 64 128 256 512), losses := [] }

theorem upper_72 : Upper D R [48,12,768,65] 13 :=
  bound_sound D R [48,12,768,65] 13 bound_72
    ((Boolean.boundCheck_true D R [48,12,768,65] 13 bound_72).mp (by decide +kernel))

def bound_73 : Bound 10 := { allowed := (rows 192 240 240 176 0 0 0 0 0 0), upper := (rows 49 14 772 74 241 241 241 241 497 753), lower := (rows 49 14 772 74 16 32 64 128 256 512), losses := [] }

theorem upper_73 : Upper D R [48,12,768,66] 13 :=
  bound_sound D R [48,12,768,66] 13 bound_73
    ((Boolean.boundCheck_true D R [48,12,768,66] 13 bound_73).mp (by decide +kernel))

def bound_74 : Bound 10 := { allowed := (rows 192 240 240 160 0 0 0 0 0 0), upper := (rows 49 14 772 88 243 227 227 227 483 739), lower := (rows 49 14 772 88 16 32 64 128 256 512), losses := [] }

theorem upper_74 : Upper D R [48,12,768,80] 13 :=
  bound_sound D R [48,12,768,80] 13 bound_74
    ((Boolean.boundCheck_true D R [48,12,768,80] 13 bound_74).mp (by decide +kernel))

def bound_75 : Bound 10 := { allowed := (rows 192 240 240 48 0 0 0 0 0 0), upper := (rows 49 14 772 200 243 243 243 243 499 755), lower := (rows 49 14 772 200 16 32 64 128 256 512), losses := [] }

theorem upper_75 : Upper D R [48,12,768,192] 13 :=
  bound_sound D R [48,12,768,192] 13 bound_75
    ((Boolean.boundCheck_true D R [48,12,768,192] 13 bound_75).mp (by decide +kernel))

def route_59 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_59 : Upper D R [48,12,768] 13 := by
  apply routed_branch D R [48,12,768] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192] route_59
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,12,768] (choices 2) [3,17,18,48,65,66,80,192] route_59).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_60
  · exact upper_69
  · exact upper_70
  · exact upper_71
  · exact upper_72
  · exact upper_73
  · exact upper_74
  · exact upper_75

def route_0 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 513 => (257,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 514 => (258,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 544 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [48,12] 13 := by
  apply routed_branch D R [48,12] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192,257,258,272,320,768] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [48,12] (choices 2) [3,17,18,48,65,66,80,192,257,258,272,320,768] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_16
  · exact upper_17
  · exact upper_18
  · exact upper_19
  · exact upper_20
  · exact upper_21
  · exact upper_22
  · exact upper_23
  · exact upper_40
  · exact upper_57
  · exact upper_58
  · exact upper_59

theorem upper : Upper D R [48,12] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case22
