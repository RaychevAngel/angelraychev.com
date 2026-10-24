import IrregularTen14Base

namespace Delivery.IrregularTen14.Case42
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 224 240 224 0 0 0 0 0 0), upper := (rows 259 530 13 28 240 224 224 224 480 736), lower := (rows 259 530 13 28 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 4 8 0 1023 1023 1023 1023 1023), good := (rows 995 995 1005 1004 992 992 992 992 992 992) }] }

theorem upper_2 : Upper D R [258,528,9,20] 13 :=
  bound_sound D R [258,528,9,20] 13 bound_2
    ((Boolean.boundCheck_true D R [258,528,9,20] 13 bound_2).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 208 192 240 208 0 0 0 0 0 0), upper := (rows 259 530 13 44 48 240 208 208 464 720), lower := (rows 259 530 13 44 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 19 18 4 8 16 0 82 146 274 530), good := (rows 963 979 13 12 979 0 64 128 256 512) }] }

theorem upper_4 : Upper D R [258,528,9,36,32] 13 :=
  bound_sound D R [258,528,9,36,32] 13 bound_4
    ((Boolean.boundCheck_true D R [258,528,9,36,32] 13 bound_4).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 240 224 176 144 0 0 0 0 0 0), upper := (rows 259 530 13 44 80 48 224 224 480 736), lower := (rows 259 530 13 44 80 48 64 128 256 512), losses := [{ target := 6, region := (rows 1 2 5 9 16 50 0 128 256 512), good := (rows 303 562 13 44 48 48 0 128 256 512) }] }

theorem upper_6 : Upper D R [258,528,9,36,64,16] 13 :=
  bound_sound D R [258,528,9,36,64,16] 13 bound_6
    ((Boolean.boundCheck_true D R [258,528,9,36,64,16] 13 bound_6).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 259 530 13 44 80 96 80 160 416 672), lower := (rows 259 530 13 44 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 7 10 0 112 64 250 378 634), good := (rows 911 943 909 940 992 992 992 128 256 512) }] }

theorem upper_8 : Upper D R [258,528,9,36,64,64,16] 13 :=
  bound_sound D R [258,528,9,36,64,64,16] 13 bound_8
    ((Boolean.boundCheck_true D R [258,528,9,36,64,64,16] 13 bound_8).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 240 224 224 192 0 0 0 0 0 0), upper := (rows 259 530 13 44 80 96 96 144 400 656), lower := (rows 259 530 13 44 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 5 13 0 1023 1023 128 256 512), good := (rows 367 610 109 108 96 96 96 224 352 608) }] }

theorem upper_9 : Upper D R [258,528,9,36,64,64,32] 13 :=
  bound_sound D R [258,528,9,36,64,64,32] 13 bound_9
    ((Boolean.boundCheck_true D R [258,528,9,36,64,64,32] 13 bound_9).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 240 192 240 208 0 0 0 0 0 0), upper := (rows 259 530 13 44 80 96 192 144 416 672), lower := (rows 259 530 13 44 80 96 192 144 256 512), losses := [{ target := 5, region := (rows 1 514 4 8 1023 0 1023 1023 256 512), good := (rows 467 722 221 220 208 208 208 208 464 722) }] }

theorem upper_11 : Upper D R [258,528,9,36,64,64,128,16] 13 :=
  bound_sound D R [258,528,9,36,64,64,128,16] 13 bound_11
    ((Boolean.boundCheck_true D R [258,528,9,36,64,64,128,16] 13 bound_11).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 240 224 224 192 0 0 0 0 0 0), upper := (rows 259 530 13 44 80 96 192 160 400 656), lower := (rows 259 530 13 44 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 5 13 0 1023 1023 1023 256 512), good := (rows 495 738 237 236 224 224 224 224 480 736) }] }

theorem upper_12 : Upper D R [258,528,9,36,64,64,128,32] 13 :=
  bound_sound D R [258,528,9,36,64,64,128,32] 13 bound_12
    ((Boolean.boundCheck_true D R [258,528,9,36,64,64,128,32] 13 bound_12).mp (by decide +kernel))

def route_10 : Route 10 := (fun mask => (mask,id))

theorem upper_10 : Upper D R [258,528,9,36,64,64,128] 13 := by
  apply routed_branch D R [258,528,9,36,64,64,128] 13 (by decide) (choices 1) [16,32] route_10
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,528,9,36,64,64,128] (choices 1) [16,32] route_10).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_11
  · exact upper_12

def route_7 : Route 10 := (fun mask => (mask,id))

theorem upper_7 : Upper D R [258,528,9,36,64,64] 13 := by
  apply routed_branch D R [258,528,9,36,64,64] 13 (by decide) (choices 1) [16,32,128] route_7
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,528,9,36,64,64] (choices 1) [16,32,128] route_7).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_8
  · exact upper_9
  · exact upper_10

def bound_14 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 259 530 13 44 80 160 80 224 480 736), lower := (rows 259 530 13 44 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 7 11 0 242 64 208 336 592), good := (rows 303 943 13 44 992 160 992 160 256 512) }] }

theorem upper_14 : Upper D R [258,528,9,36,64,128,16] 13 :=
  bound_sound D R [258,528,9,36,64,128,16] 13 bound_14
    ((Boolean.boundCheck_true D R [258,528,9,36,64,128,16] 13 bound_14).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 208 192 240 208 0 0 0 0 0 0), upper := (rows 259 530 13 44 80 160 96 208 464 720), lower := (rows 259 530 13 44 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 83 82 4 8 80 0 64 208 336 592), good := (rows 259 915 13 12 979 128 979 128 256 512) }] }

theorem upper_15 : Upper D R [258,528,9,36,64,128,32] 13 :=
  bound_sound D R [258,528,9,36,64,128,32] 13 bound_15
    ((Boolean.boundCheck_true D R [258,528,9,36,64,128,32] 13 bound_15).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 224 224 240 208 0 0 0 0 0 0), upper := (rows 259 530 13 44 80 160 192 144 352 608), lower := (rows 259 530 13 44 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 3 2 4 8 0 224 224 128 504 760), good := (rows 259 771 781 876 864 992 992 992 256 512) }] }

theorem upper_17 : Upper D R [258,528,9,36,64,128,128,16] 13 :=
  bound_sound D R [258,528,9,36,64,128,128,16] 13 bound_17
    ((Boolean.boundCheck_true D R [258,528,9,36,64,128,128,16] 13 bound_17).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 240 224 224 192 0 0 0 0 0 0), upper := (rows 259 530 13 44 80 160 192 160 336 592), lower := (rows 259 530 13 44 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 5 13 0 1023 1023 1023 256 512), good := (rows 495 738 237 236 224 224 224 224 480 736) }] }

theorem upper_18 : Upper D R [258,528,9,36,64,128,128,32] 13 :=
  bound_sound D R [258,528,9,36,64,128,128,32] 13 bound_18
    ((Boolean.boundCheck_true D R [258,528,9,36,64,128,128,32] 13 bound_18).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 240 224 224 192 0 0 0 0 0 0), upper := (rows 259 530 13 44 80 160 192 192 304 560), lower := (rows 259 530 13 44 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 5 13 0 1023 1023 1023 256 512), good := (rows 495 738 237 236 224 224 224 224 480 736) }] }

theorem upper_19 : Upper D R [258,528,9,36,64,128,128,64] 13 :=
  bound_sound D R [258,528,9,36,64,128,128,64] 13 bound_19
    ((Boolean.boundCheck_true D R [258,528,9,36,64,128,128,64] 13 bound_19).mp (by decide +kernel))

def route_16 : Route 10 := (fun mask => (mask,id))

theorem upper_16 : Upper D R [258,528,9,36,64,128,128] 13 := by
  apply routed_branch D R [258,528,9,36,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_16
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,528,9,36,64,128,128] (choices 1) [16,32,64] route_16).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_17
  · exact upper_18
  · exact upper_19

def route_13 : Route 10 := (fun mask => (mask,id))

theorem upper_13 : Upper D R [258,528,9,36,64,128] 13 := by
  apply routed_branch D R [258,528,9,36,64,128] 13 (by decide) (choices 1) [16,32,128] route_13
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,528,9,36,64,128] (choices 1) [16,32,128] route_13).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_14
  · exact upper_15
  · exact upper_16

def route_5 : Route 10 := (fun mask => (mask,id))

theorem upper_5 : Upper D R [258,528,9,36,64] 13 := by
  apply routed_branch D R [258,528,9,36,64] 13 (by decide) (choices 1) [16,64,128] route_5
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,528,9,36,64] (choices 1) [16,64,128] route_5).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_6
  · exact upper_7
  · exact upper_13

def route_3 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_3 : Upper D R [258,528,9,36] 13 := by
  apply routed_branch D R [258,528,9,36] 13 (by decide) (choices 1) [32,64] route_3
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,528,9,36] (choices 1) [32,64] route_3).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_4
  · exact upper_5

def bound_20 : Bound 10 := { allowed := (rows 240 224 240 192 0 0 0 0 0 0), upper := (rows 259 530 13 56 244 228 228 228 484 740), lower := (rows 259 530 13 56 16 32 64 128 256 512), losses := [] }

theorem upper_20 : Upper D R [258,528,9,48] 13 :=
  bound_sound D R [258,528,9,48] 13 bound_20
    ((Boolean.boundCheck_true D R [258,528,9,48] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 240 224 240 144 0 0 0 0 0 0), upper := (rows 259 530 13 104 244 244 244 244 500 756), lower := (rows 259 530 13 104 16 32 64 128 256 512), losses := [] }

theorem upper_21 : Upper D R [258,528,9,96] 13 :=
  bound_sound D R [258,528,9,96] 13 bound_21
    ((Boolean.boundCheck_true D R [258,528,9,96] 13 bound_21).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [258,528,9] 13 := by
  apply routed_branch D R [258,528,9] 13 (by decide) (choices 2) [20,36,48,96] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,528,9] (choices 2) [20,36,48,96] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_20
  · exact upper_21

def bound_23 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 259 530 21 44 248 232 232 232 488 744), lower := (rows 259 530 21 44 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [258,528,17,36] 13 :=
  bound_sound D R [258,528,17,36] 13 bound_23
    ((Boolean.boundCheck_true D R [258,528,17,36] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 240 224 224 144 0 0 0 0 0 0), upper := (rows 259 530 21 104 252 236 236 236 492 748), lower := (rows 259 530 21 104 16 32 64 128 256 512), losses := [] }

theorem upper_24 : Upper D R [258,528,17,96] 13 :=
  bound_sound D R [258,528,17,96] 13 bound_24
    ((Boolean.boundCheck_true D R [258,528,17,96] 13 bound_24).mp (by decide +kernel))

def route_22 : Route 10 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_22 : Upper D R [258,528,17] 13 := by
  apply routed_branch D R [258,528,17] 13 (by decide) (choices 2) [36,96] route_22
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,528,17] (choices 2) [36,96] route_22).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_23
  · exact upper_24

def bound_26 : Bound 10 := { allowed := (rows 224 224 224 240 0 0 0 0 0 0), upper := (rows 259 530 28 13 240 224 224 224 480 736), lower := (rows 259 530 28 13 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 4 8 0 1023 1023 1023 1023 1023), good := (rows 995 995 1004 1005 992 992 992 992 992 992) }] }

theorem upper_26 : Upper D R [258,528,24,5] 13 :=
  bound_sound D R [258,528,24,5] 13 bound_26
    ((Boolean.boundCheck_true D R [258,528,24,5] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 259 530 28 41 244 228 228 228 484 740), lower := (rows 259 530 28 41 16 32 64 128 256 512), losses := [] }

theorem upper_27 : Upper D R [258,528,24,33] 13 :=
  bound_sound D R [258,528,24,33] 13 bound_27
    ((Boolean.boundCheck_true D R [258,528,24,33] 13 bound_27).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 259 530 28 44 241 225 225 225 481 737), lower := (rows 259 530 28 44 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [258,528,24,36] 13 :=
  bound_sound D R [258,528,24,36] 13 bound_28
    ((Boolean.boundCheck_true D R [258,528,24,36] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 240 224 224 144 0 0 0 0 0 0), upper := (rows 259 530 28 104 245 229 229 229 485 741), lower := (rows 259 530 28 104 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [258,528,24,96] 13 :=
  bound_sound D R [258,528,24,96] 13 bound_29
    ((Boolean.boundCheck_true D R [258,528,24,96] 13 bound_29).mp (by decide +kernel))

def route_25 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_25 : Upper D R [258,528,24] 13 := by
  apply routed_branch D R [258,528,24] 13 (by decide) (choices 2) [5,33,36,96] route_25
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,528,24] (choices 2) [5,33,36,96] route_25).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_26
  · exact upper_27
  · exact upper_28
  · exact upper_29

def bound_31 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 259 530 37 28 248 232 232 232 488 744), lower := (rows 259 530 37 28 16 32 64 128 256 512), losses := [] }

theorem upper_31 : Upper D R [258,528,33,20] 13 :=
  bound_sound D R [258,528,33,20] 13 bound_31
    ((Boolean.boundCheck_true D R [258,528,33,20] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 240 224 208 208 0 0 0 0 0 0), upper := (rows 259 530 37 44 216 248 216 216 472 728), lower := (rows 259 530 37 44 16 32 64 128 256 512), losses := [] }

theorem upper_32 : Upper D R [258,528,33,36] 13 :=
  bound_sound D R [258,528,33,36] 13 bound_32
    ((Boolean.boundCheck_true D R [258,528,33,36] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 240 224 208 192 0 0 0 0 0 0), upper := (rows 259 530 37 56 220 236 204 204 460 716), lower := (rows 259 530 37 56 16 32 64 128 256 512), losses := [] }

theorem upper_33 : Upper D R [258,528,33,48] 13 :=
  bound_sound D R [258,528,33,48] 13 bound_33
    ((Boolean.boundCheck_true D R [258,528,33,48] 13 bound_33).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 240 224 208 176 0 0 0 0 0 0), upper := (rows 259 530 37 76 248 248 248 248 504 760), lower := (rows 259 530 37 76 16 32 64 128 256 512), losses := [] }

theorem upper_34 : Upper D R [258,528,33,68] 13 :=
  bound_sound D R [258,528,33,68] 13 bound_34
    ((Boolean.boundCheck_true D R [258,528,33,68] 13 bound_34).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 240 224 208 160 0 0 0 0 0 0), upper := (rows 259 530 37 88 252 236 236 236 492 748), lower := (rows 259 530 37 88 16 32 64 128 256 512), losses := [] }

theorem upper_35 : Upper D R [258,528,33,80] 13 :=
  bound_sound D R [258,528,33,80] 13 bound_35
    ((Boolean.boundCheck_true D R [258,528,33,80] 13 bound_35).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 240 224 208 144 0 0 0 0 0 0), upper := (rows 259 530 37 104 220 252 220 220 476 732), lower := (rows 259 530 37 104 16 32 64 128 256 512), losses := [] }

theorem upper_36 : Upper D R [258,528,33,96] 13 :=
  bound_sound D R [258,528,33,96] 13 bound_36
    ((Boolean.boundCheck_true D R [258,528,33,96] 13 bound_36).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 240 224 208 48 0 0 0 0 0 0), upper := (rows 259 530 37 200 252 252 252 252 508 764), lower := (rows 259 530 37 200 16 32 64 128 256 512), losses := [] }

theorem upper_37 : Upper D R [258,528,33,192] 13 :=
  bound_sound D R [258,528,33,192] 13 bound_37
    ((Boolean.boundCheck_true D R [258,528,33,192] 13 bound_37).mp (by decide +kernel))

def route_30 : Route 10 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_30 : Upper D R [258,528,33] 13 := by
  apply routed_branch D R [258,528,33] 13 (by decide) (choices 2) [20,36,48,68,80,96,192] route_30
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,528,33] (choices 2) [20,36,48,68,80,96,192] route_30).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_31
  · exact upper_32
  · exact upper_33
  · exact upper_34
  · exact upper_35
  · exact upper_36
  · exact upper_37

def bound_40 : Bound 10 := { allowed := (rows 208 192 208 240 0 0 0 0 0 0), upper := (rows 259 530 44 13 48 240 208 208 464 720), lower := (rows 259 530 44 13 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 19 18 4 8 16 0 82 146 274 530), good := (rows 963 979 12 13 979 0 64 128 256 512) }] }

theorem upper_40 : Upper D R [258,528,40,5,32] 13 :=
  bound_sound D R [258,528,40,5,32] 13 bound_40
    ((Boolean.boundCheck_true D R [258,528,40,5,32] 13 bound_40).mp (by decide +kernel))

def bound_42 : Bound 10 := { allowed := (rows 240 224 144 176 0 0 0 0 0 0), upper := (rows 259 530 44 13 80 48 224 224 480 736), lower := (rows 259 530 44 13 80 48 64 128 256 512), losses := [{ target := 6, region := (rows 1 2 5 9 16 50 0 128 256 512), good := (rows 303 562 44 13 48 48 0 128 256 512) }] }

theorem upper_42 : Upper D R [258,528,40,5,64,16] 13 :=
  bound_sound D R [258,528,40,5,64,16] 13 bound_42
    ((Boolean.boundCheck_true D R [258,528,40,5,64,16] 13 bound_42).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 259 530 44 13 80 96 80 160 416 672), lower := (rows 259 530 44 13 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 6 11 0 112 64 246 374 630), good := (rows 911 943 940 909 992 992 992 128 256 512) }] }

theorem upper_44 : Upper D R [258,528,40,5,64,64,16] 13 :=
  bound_sound D R [258,528,40,5,64,64,16] 13 bound_44
    ((Boolean.boundCheck_true D R [258,528,40,5,64,64,16] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 240 224 192 224 0 0 0 0 0 0), upper := (rows 259 530 44 13 80 96 96 144 400 656), lower := (rows 259 530 44 13 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 13 9 0 1023 1023 128 256 512), good := (rows 367 610 108 109 96 96 96 224 352 608) }] }

theorem upper_45 : Upper D R [258,528,40,5,64,64,32] 13 :=
  bound_sound D R [258,528,40,5,64,64,32] 13 bound_45
    ((Boolean.boundCheck_true D R [258,528,40,5,64,64,32] 13 bound_45).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 240 192 208 240 0 0 0 0 0 0), upper := (rows 259 530 44 13 80 96 192 144 416 672), lower := (rows 259 530 44 13 80 96 192 144 256 512), losses := [{ target := 5, region := (rows 1 514 4 8 1023 0 1023 1023 256 512), good := (rows 467 722 220 221 208 208 208 208 464 722) }] }

theorem upper_47 : Upper D R [258,528,40,5,64,64,128,16] 13 :=
  bound_sound D R [258,528,40,5,64,64,128,16] 13 bound_47
    ((Boolean.boundCheck_true D R [258,528,40,5,64,64,128,16] 13 bound_47).mp (by decide +kernel))

def bound_48 : Bound 10 := { allowed := (rows 240 224 192 224 0 0 0 0 0 0), upper := (rows 259 530 44 13 80 96 192 160 400 656), lower := (rows 259 530 44 13 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 13 9 0 1023 1023 1023 256 512), good := (rows 495 738 236 237 224 224 224 224 480 736) }] }

theorem upper_48 : Upper D R [258,528,40,5,64,64,128,32] 13 :=
  bound_sound D R [258,528,40,5,64,64,128,32] 13 bound_48
    ((Boolean.boundCheck_true D R [258,528,40,5,64,64,128,32] 13 bound_48).mp (by decide +kernel))

def route_46 : Route 10 := (fun mask => (mask,id))

theorem upper_46 : Upper D R [258,528,40,5,64,64,128] 13 := by
  apply routed_branch D R [258,528,40,5,64,64,128] 13 (by decide) (choices 1) [16,32] route_46
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,528,40,5,64,64,128] (choices 1) [16,32] route_46).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_47
  · exact upper_48

def route_43 : Route 10 := (fun mask => (mask,id))

theorem upper_43 : Upper D R [258,528,40,5,64,64] 13 := by
  apply routed_branch D R [258,528,40,5,64,64] 13 (by decide) (choices 1) [16,32,128] route_43
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,528,40,5,64,64] (choices 1) [16,32,128] route_43).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_44
  · exact upper_45
  · exact upper_46

def bound_50 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 259 530 44 13 80 160 80 224 480 736), lower := (rows 259 530 44 13 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 7 11 0 242 64 208 336 592), good := (rows 303 943 44 13 992 160 992 160 256 512) }] }

theorem upper_50 : Upper D R [258,528,40,5,64,128,16] 13 :=
  bound_sound D R [258,528,40,5,64,128,16] 13 bound_50
    ((Boolean.boundCheck_true D R [258,528,40,5,64,128,16] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 208 192 208 240 0 0 0 0 0 0), upper := (rows 259 530 44 13 80 160 96 208 464 720), lower := (rows 259 530 44 13 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 83 82 4 8 80 0 64 208 336 592), good := (rows 259 915 12 13 979 128 979 128 256 512) }] }

theorem upper_51 : Upper D R [258,528,40,5,64,128,32] 13 :=
  bound_sound D R [258,528,40,5,64,128,32] 13 bound_51
    ((Boolean.boundCheck_true D R [258,528,40,5,64,128,32] 13 bound_51).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 224 224 208 240 0 0 0 0 0 0), upper := (rows 259 530 44 13 80 160 192 144 352 608), lower := (rows 259 530 44 13 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 3 2 4 8 0 224 224 128 500 756), good := (rows 259 771 876 781 864 992 992 992 256 512) }] }

theorem upper_53 : Upper D R [258,528,40,5,64,128,128,16] 13 :=
  bound_sound D R [258,528,40,5,64,128,128,16] 13 bound_53
    ((Boolean.boundCheck_true D R [258,528,40,5,64,128,128,16] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 240 224 192 224 0 0 0 0 0 0), upper := (rows 259 530 44 13 80 160 192 160 336 592), lower := (rows 259 530 44 13 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 13 9 0 1023 1023 1023 256 512), good := (rows 495 738 236 237 224 224 224 224 480 736) }] }

theorem upper_54 : Upper D R [258,528,40,5,64,128,128,32] 13 :=
  bound_sound D R [258,528,40,5,64,128,128,32] 13 bound_54
    ((Boolean.boundCheck_true D R [258,528,40,5,64,128,128,32] 13 bound_54).mp (by decide +kernel))

def bound_55 : Bound 10 := { allowed := (rows 240 224 192 224 0 0 0 0 0 0), upper := (rows 259 530 44 13 80 160 192 192 304 560), lower := (rows 259 530 44 13 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 13 9 0 1023 1023 1023 256 512), good := (rows 495 738 236 237 224 224 224 224 480 736) }] }

theorem upper_55 : Upper D R [258,528,40,5,64,128,128,64] 13 :=
  bound_sound D R [258,528,40,5,64,128,128,64] 13 bound_55
    ((Boolean.boundCheck_true D R [258,528,40,5,64,128,128,64] 13 bound_55).mp (by decide +kernel))

def route_52 : Route 10 := (fun mask => (mask,id))

theorem upper_52 : Upper D R [258,528,40,5,64,128,128] 13 := by
  apply routed_branch D R [258,528,40,5,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_52
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,528,40,5,64,128,128] (choices 1) [16,32,64] route_52).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_53
  · exact upper_54
  · exact upper_55

def route_49 : Route 10 := (fun mask => (mask,id))

theorem upper_49 : Upper D R [258,528,40,5,64,128] 13 := by
  apply routed_branch D R [258,528,40,5,64,128] 13 (by decide) (choices 1) [16,32,128] route_49
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,528,40,5,64,128] (choices 1) [16,32,128] route_49).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_50
  · exact upper_51
  · exact upper_52

def route_41 : Route 10 := (fun mask => (mask,id))

theorem upper_41 : Upper D R [258,528,40,5,64] 13 := by
  apply routed_branch D R [258,528,40,5,64] 13 (by decide) (choices 1) [16,64,128] route_41
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,528,40,5,64] (choices 1) [16,64,128] route_41).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_42
  · exact upper_43
  · exact upper_49

def route_39 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_39 : Upper D R [258,528,40,5] 13 := by
  apply routed_branch D R [258,528,40,5] 13 (by decide) (choices 1) [32,64] route_39
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [258,528,40,5] (choices 1) [32,64] route_39).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_40
  · exact upper_41

def bound_56 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 259 530 44 25 244 228 228 228 484 740), lower := (rows 259 530 44 25 16 32 64 128 256 512), losses := [] }

theorem upper_56 : Upper D R [258,528,40,17] 13 :=
  bound_sound D R [258,528,40,17] 13 bound_56
    ((Boolean.boundCheck_true D R [258,528,40,17] 13 bound_56).mp (by decide +kernel))

def bound_57 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 259 530 44 28 241 225 225 225 481 737), lower := (rows 259 530 44 28 16 32 64 128 256 512), losses := [] }

theorem upper_57 : Upper D R [258,528,40,20] 13 :=
  bound_sound D R [258,528,40,20] 13 bound_57
    ((Boolean.boundCheck_true D R [258,528,40,20] 13 bound_57).mp (by decide +kernel))

def bound_58 : Bound 10 := { allowed := (rows 240 224 208 208 0 0 0 0 0 0), upper := (rows 259 530 44 41 212 244 212 212 468 724), lower := (rows 259 530 44 41 16 32 64 128 256 512), losses := [] }

theorem upper_58 : Upper D R [258,528,40,33] 13 :=
  bound_sound D R [258,528,40,33] 13 bound_58
    ((Boolean.boundCheck_true D R [258,528,40,33] 13 bound_58).mp (by decide +kernel))

def bound_59 : Bound 10 := { allowed := (rows 240 224 208 208 0 0 0 0 0 0), upper := (rows 259 530 44 44 209 241 209 209 465 721), lower := (rows 259 530 44 44 16 32 64 128 256 512), losses := [] }

theorem upper_59 : Upper D R [258,528,40,36] 13 :=
  bound_sound D R [258,528,40,36] 13 bound_59
    ((Boolean.boundCheck_true D R [258,528,40,36] 13 bound_59).mp (by decide +kernel))

def bound_60 : Bound 10 := { allowed := (rows 240 224 208 192 0 0 0 0 0 0), upper := (rows 259 530 44 56 213 229 197 197 453 709), lower := (rows 259 530 44 56 16 32 64 128 256 512), losses := [] }

theorem upper_60 : Upper D R [258,528,40,48] 13 :=
  bound_sound D R [258,528,40,48] 13 bound_60
    ((Boolean.boundCheck_true D R [258,528,40,48] 13 bound_60).mp (by decide +kernel))

def bound_61 : Bound 10 := { allowed := (rows 240 224 208 176 0 0 0 0 0 0), upper := (rows 259 530 44 73 244 244 244 244 500 756), lower := (rows 259 530 44 73 16 32 64 128 256 512), losses := [] }

theorem upper_61 : Upper D R [258,528,40,65] 13 :=
  bound_sound D R [258,528,40,65] 13 bound_61
    ((Boolean.boundCheck_true D R [258,528,40,65] 13 bound_61).mp (by decide +kernel))

def bound_62 : Bound 10 := { allowed := (rows 240 224 208 176 0 0 0 0 0 0), upper := (rows 259 530 44 76 241 241 241 241 497 753), lower := (rows 259 530 44 76 16 32 64 128 256 512), losses := [] }

theorem upper_62 : Upper D R [258,528,40,68] 13 :=
  bound_sound D R [258,528,40,68] 13 bound_62
    ((Boolean.boundCheck_true D R [258,528,40,68] 13 bound_62).mp (by decide +kernel))

def bound_63 : Bound 10 := { allowed := (rows 240 224 208 160 0 0 0 0 0 0), upper := (rows 259 530 44 88 245 229 229 229 485 741), lower := (rows 259 530 44 88 16 32 64 128 256 512), losses := [] }

theorem upper_63 : Upper D R [258,528,40,80] 13 :=
  bound_sound D R [258,528,40,80] 13 bound_63
    ((Boolean.boundCheck_true D R [258,528,40,80] 13 bound_63).mp (by decide +kernel))

def bound_64 : Bound 10 := { allowed := (rows 240 224 208 144 0 0 0 0 0 0), upper := (rows 259 530 44 104 213 245 213 213 469 725), lower := (rows 259 530 44 104 16 32 64 128 256 512), losses := [] }

theorem upper_64 : Upper D R [258,528,40,96] 13 :=
  bound_sound D R [258,528,40,96] 13 bound_64
    ((Boolean.boundCheck_true D R [258,528,40,96] 13 bound_64).mp (by decide +kernel))

def bound_65 : Bound 10 := { allowed := (rows 240 224 208 48 0 0 0 0 0 0), upper := (rows 259 530 44 200 245 245 245 245 501 757), lower := (rows 259 530 44 200 16 32 64 128 256 512), losses := [] }

theorem upper_65 : Upper D R [258,528,40,192] 13 :=
  bound_sound D R [258,528,40,192] 13 bound_65
    ((Boolean.boundCheck_true D R [258,528,40,192] 13 bound_65).mp (by decide +kernel))

def route_38 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_38 : Upper D R [258,528,40] 13 := by
  apply routed_branch D R [258,528,40] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192] route_38
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,528,40] (choices 2) [5,17,20,33,36,48,65,68,80,96,192] route_38).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_39
  · exact upper_56
  · exact upper_57
  · exact upper_58
  · exact upper_59
  · exact upper_60
  · exact upper_61
  · exact upper_62
  · exact upper_63
  · exact upper_64
  · exact upper_65

def bound_66 : Bound 10 := { allowed := (rows 240 224 192 240 0 0 0 0 0 0), upper := (rows 259 530 52 237 253 237 237 237 493 749), lower := (rows 259 530 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_66 : Upper D R [258,528,48] 13 :=
  bound_sound D R [258,528,48] 13 bound_66
    ((Boolean.boundCheck_true D R [258,528,48] 13 bound_66).mp (by decide +kernel))

def bound_67 : Bound 10 := { allowed := (rows 240 224 144 240 0 0 0 0 0 0), upper := (rows 259 530 100 253 253 253 253 253 509 765), lower := (rows 259 530 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_67 : Upper D R [258,528,96] 13 :=
  bound_sound D R [258,528,96] 13 bound_67
    ((Boolean.boundCheck_true D R [258,528,96] 13 bound_67).mp (by decide +kernel))

def route_0 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [258,528] 13 := by
  apply routed_branch D R [258,528] 13 (by decide) (choices 2) [9,17,24,33,40,48,96] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [258,528] (choices 2) [9,17,24,33,40,48,96] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_22
  · exact upper_25
  · exact upper_30
  · exact upper_38
  · exact upper_66
  · exact upper_67

theorem upper : Upper D R [258,528] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case42
