import RobustTwoMove

/-! Six explicit arbitrary-subset dense envelopes, orders16 through21.
Data are explicit and every safe intermediary is checked by Lean's kernel.
The conditional graph envelope theorem quantifies over EVERY intermediate
graph, not just a single graph at each arc count. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SmallDenseEnvelopes

def baseMissing (n : Nat) : List (Nat × Nat) :=
  match n with
  | 16 => [(0,8), (0,15), (1,8), (1,9), (2,9), (2,10), (3,10), (3,11), (4,11), (4,12), (5,12), (5,13), (6,13), (6,14), (7,14), (7,15), (8,4), (8,6), (9,5), (9,7), (10,0), (10,6), (11,1), (11,7), (12,0), (12,2), (13,1), (13,3), (14,2), (14,4), (15,3), (15,5)]
  | 17 => [(0,15), (0,16), (1,8), (1,9), (2,9), (2,10), (3,10), (3,16), (4,11), (4,12), (5,12), (5,13), (6,13), (6,14), (7,14), (7,15), (8,4), (8,6), (9,5), (9,7), (10,0), (10,6), (11,1), (11,7), (12,0), (12,2), (13,1), (13,3), (14,2), (14,4), (15,3), (15,5), (16,8), (16,11)]
  | 18 => [(0,9), (0,17), (1,9), (1,10), (2,10), (2,11), (3,11), (3,12), (4,12), (4,13), (5,13), (5,14), (6,14), (6,15), (7,15), (7,16), (8,16), (8,17), (9,4), (9,6), (10,5), (10,7), (11,6), (11,8), (12,0), (12,7), (13,1), (13,8), (14,0), (14,2), (15,1), (15,3), (16,2), (16,4), (17,3), (17,5)]
  | 19 => [(0,17), (0,18), (1,9), (1,10), (2,10), (2,11), (3,11), (3,18), (4,12), (4,13), (5,13), (5,14), (6,14), (6,15), (7,15), (7,16), (8,16), (8,17), (9,4), (9,6), (10,5), (10,7), (11,6), (11,8), (12,0), (12,7), (13,1), (13,8), (14,0), (14,2), (15,1), (15,3), (16,2), (16,4), (17,3), (17,5), (18,9), (18,12)]
  | 20 => [(0,10), (0,19), (1,10), (1,11), (2,11), (2,12), (3,12), (3,13), (4,13), (4,14), (5,14), (5,15), (6,15), (6,16), (7,16), (7,17), (8,17), (8,18), (9,18), (9,19), (10,4), (10,6), (11,5), (11,7), (12,6), (12,8), (13,7), (13,9), (14,0), (14,8), (15,1), (15,9), (16,0), (16,2), (17,1), (17,3), (18,2), (18,4), (19,3), (19,5)]
  | 21 => [(0,19), (0,20), (1,10), (1,11), (2,11), (2,12), (3,12), (3,20), (4,13), (4,14), (5,14), (5,15), (6,15), (6,16), (7,16), (7,17), (8,17), (8,18), (9,18), (9,19), (10,4), (10,6), (11,5), (11,7), (12,6), (12,8), (13,7), (13,9), (14,0), (14,8), (15,1), (15,9), (16,0), (16,2), (17,1), (17,3), (18,2), (18,4), (19,3), (19,5), (20,10), (20,13)]
  | _ => []

def optionalMissing (n : Nat) : List (Nat × Nat) :=
  match n with
  | 16 => [(0,12), (1,13), (2,13), (3,15), (4,15), (5,9), (6,10), (7,10), (8,1), (9,2), (10,3), (11,4), (12,5), (13,6), (14,7), (15,0)]
  | 17 => [(0,7), (0,11), (1,13), (2,14), (3,14), (4,16), (5,9), (6,8), (7,10), (8,3), (10,3), (12,5), (13,6), (14,10), (15,6), (16,1), (16,13)]
  | 18 => [(0,12), (0,14), (1,14), (2,15), (3,16), (4,16), (5,17), (6,9), (7,10), (8,11), (8,13), (9,0), (10,1), (11,2), (12,3), (12,4), (13,5), (14,6)]
  | 19 => [(0,3), (0,12), (1,2), (2,15), (3,15), (4,5), (5,9), (6,10), (6,18), (7,11), (8,11), (8,13), (12,18), (13,4), (14,6), (15,10), (16,9), (17,8), (17,13)]
  | 20 => [(0,13), (0,16), (1,14), (2,15), (3,18), (4,10), (4,18), (5,10), (9,12), (9,15), (10,9), (11,17), (12,2), (13,3), (13,17), (14,5), (15,6), (17,11), (18,14), (19,8)]
  | 21 => [(0,3), (1,14), (1,16), (2,18), (3,18), (6,11), (7,11), (8,12), (8,14), (9,12), (11,1), (11,15), (12,2), (13,20), (15,6), (15,19), (17,6), (17,7), (18,8), (18,10), (18,14)]
  | _ => []

def fullMask (n s : Nat) : Nat :=
  match n, s with
  | 16, 0 => 37120
  | 16, 1 => 8960
  | 16, 2 => 9728
  | 16, 3 => 35840
  | 16, 4 => 38912
  | 16, 5 => 12800
  | 16, 6 => 25600
  | 16, 7 => 50176
  | 16, 8 => 82
  | 16, 9 => 164
  | 16, 10 => 73
  | 16, 11 => 146
  | 16, 12 => 37
  | 16, 13 => 74
  | 16, 14 => 148
  | 16, 15 => 41
  | 17, 0 => 100480
  | 17, 1 => 8960
  | 17, 2 => 17920
  | 17, 3 => 82944
  | 17, 4 => 71680
  | 17, 5 => 12800
  | 17, 6 => 24832
  | 17, 7 => 50176
  | 17, 8 => 88
  | 17, 9 => 160
  | 17, 10 => 73
  | 17, 11 => 130
  | 17, 12 => 37
  | 17, 13 => 74
  | 17, 14 => 1044
  | 17, 15 => 104
  | 17, 16 => 10498
  | 18, 0 => 152064
  | 18, 1 => 17920
  | 18, 2 => 35840
  | 18, 3 => 71680
  | 18, 4 => 77824
  | 18, 5 => 155648
  | 18, 6 => 49664
  | 18, 7 => 99328
  | 18, 8 => 206848
  | 18, 9 => 81
  | 18, 10 => 162
  | 18, 11 => 324
  | 18, 12 => 153
  | 18, 13 => 290
  | 18, 14 => 69
  | 18, 15 => 10
  | 18, 16 => 20
  | 18, 17 => 40
  | 19, 0 => 397320
  | 19, 1 => 1540
  | 19, 2 => 35840
  | 19, 3 => 296960
  | 19, 4 => 12320
  | 19, 5 => 25088
  | 19, 6 => 312320
  | 19, 7 => 100352
  | 19, 8 => 206848
  | 19, 9 => 80
  | 19, 10 => 160
  | 19, 11 => 320
  | 19, 12 => 262273
  | 19, 13 => 274
  | 19, 14 => 69
  | 19, 15 => 1034
  | 19, 16 => 532
  | 19, 17 => 8488
  | 19, 18 => 4608
  | 20, 0 => 599040
  | 20, 1 => 19456
  | 20, 2 => 38912
  | 20, 3 => 274432
  | 20, 4 => 287744
  | 20, 5 => 50176
  | 20, 6 => 98304
  | 20, 7 => 196608
  | 20, 8 => 393216
  | 20, 9 => 823296
  | 20, 10 => 592
  | 20, 11 => 131232
  | 20, 12 => 324
  | 20, 13 => 131720
  | 20, 14 => 289
  | 20, 15 => 578
  | 20, 16 => 5
  | 20, 17 => 2058
  | 20, 18 => 16404
  | 20, 19 => 296
  | 21, 0 => 1572872
  | 21, 1 => 84992
  | 21, 2 => 268288
  | 21, 3 => 1314816
  | 21, 4 => 24576
  | 21, 5 => 49152
  | 21, 6 => 100352
  | 21, 7 => 198656
  | 21, 8 => 413696
  | 21, 9 => 790528
  | 21, 10 => 80
  | 21, 11 => 32930
  | 21, 12 => 324
  | 21, 13 => 1049216
  | 21, 14 => 257
  | 21, 15 => 524866
  | 21, 16 => 5
  | 21, 17 => 202
  | 21, 18 => 17684
  | 21, 19 => 40
  | 21, 20 => 9216
  | _, _ => 0

def baseMask (n s : Nat) : Nat :=
  match n, s with
  | 16, 0 => 33024
  | 16, 1 => 768
  | 16, 2 => 1536
  | 16, 3 => 3072
  | 16, 4 => 6144
  | 16, 5 => 12288
  | 16, 6 => 24576
  | 16, 7 => 49152
  | 16, 8 => 80
  | 16, 9 => 160
  | 16, 10 => 65
  | 16, 11 => 130
  | 16, 12 => 5
  | 16, 13 => 10
  | 16, 14 => 20
  | 16, 15 => 40
  | 17, 0 => 98304
  | 17, 1 => 768
  | 17, 2 => 1536
  | 17, 3 => 66560
  | 17, 4 => 6144
  | 17, 5 => 12288
  | 17, 6 => 24576
  | 17, 7 => 49152
  | 17, 8 => 80
  | 17, 9 => 160
  | 17, 10 => 65
  | 17, 11 => 130
  | 17, 12 => 5
  | 17, 13 => 10
  | 17, 14 => 20
  | 17, 15 => 40
  | 17, 16 => 2304
  | 18, 0 => 131584
  | 18, 1 => 1536
  | 18, 2 => 3072
  | 18, 3 => 6144
  | 18, 4 => 12288
  | 18, 5 => 24576
  | 18, 6 => 49152
  | 18, 7 => 98304
  | 18, 8 => 196608
  | 18, 9 => 80
  | 18, 10 => 160
  | 18, 11 => 320
  | 18, 12 => 129
  | 18, 13 => 258
  | 18, 14 => 5
  | 18, 15 => 10
  | 18, 16 => 20
  | 18, 17 => 40
  | 19, 0 => 393216
  | 19, 1 => 1536
  | 19, 2 => 3072
  | 19, 3 => 264192
  | 19, 4 => 12288
  | 19, 5 => 24576
  | 19, 6 => 49152
  | 19, 7 => 98304
  | 19, 8 => 196608
  | 19, 9 => 80
  | 19, 10 => 160
  | 19, 11 => 320
  | 19, 12 => 129
  | 19, 13 => 258
  | 19, 14 => 5
  | 19, 15 => 10
  | 19, 16 => 20
  | 19, 17 => 40
  | 19, 18 => 4608
  | 20, 0 => 525312
  | 20, 1 => 3072
  | 20, 2 => 6144
  | 20, 3 => 12288
  | 20, 4 => 24576
  | 20, 5 => 49152
  | 20, 6 => 98304
  | 20, 7 => 196608
  | 20, 8 => 393216
  | 20, 9 => 786432
  | 20, 10 => 80
  | 20, 11 => 160
  | 20, 12 => 320
  | 20, 13 => 640
  | 20, 14 => 257
  | 20, 15 => 514
  | 20, 16 => 5
  | 20, 17 => 10
  | 20, 18 => 20
  | 20, 19 => 40
  | 21, 0 => 1572864
  | 21, 1 => 3072
  | 21, 2 => 6144
  | 21, 3 => 1052672
  | 21, 4 => 24576
  | 21, 5 => 49152
  | 21, 6 => 98304
  | 21, 7 => 196608
  | 21, 8 => 393216
  | 21, 9 => 786432
  | 21, 10 => 80
  | 21, 11 => 160
  | 21, 12 => 320
  | 21, 13 => 640
  | 21, 14 => 257
  | 21, 15 => 514
  | 21, 16 => 5
  | 21, 17 => 10
  | 21, 18 => 20
  | 21, 19 => 40
  | 21, 20 => 9216
  | _, _ => 0

def lower (n : Nat) (s t : Fin n) : Prop :=
  s ≠ t ∧ (fullMask n s.val).testBit t.val = false

def upper (n : Nat) (s t : Fin n) : Prop :=
  s ≠ t ∧ (baseMask n s.val).testBit t.val = false

instance (n : Nat) (s t : Fin n) : Decidable (lower n s t) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (n : Nat) (s t : Fin n) : Decidable (upper n s t) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem witnesses16 :
    RobustTwoMove.Witnesses (lower 16) (upper 16) := by
  unfold RobustTwoMove.Witnesses
  decide +kernel

private theorem witnesses17 :
    RobustTwoMove.Witnesses (lower 17) (upper 17) := by
  unfold RobustTwoMove.Witnesses
  decide +kernel

private theorem witnesses18 :
    RobustTwoMove.Witnesses (lower 18) (upper 18) := by
  unfold RobustTwoMove.Witnesses
  decide +kernel

private theorem witnesses19 :
    RobustTwoMove.Witnesses (lower 19) (upper 19) := by
  unfold RobustTwoMove.Witnesses
  decide +kernel

private theorem witnesses20 :
    RobustTwoMove.Witnesses (lower 20) (upper 20) := by
  unfold RobustTwoMove.Witnesses
  decide +kernel

private theorem witnesses21 :
    RobustTwoMove.Witnesses (lower 21) (upper 21) := by
  unfold RobustTwoMove.Witnesses
  decide +kernel

theorem witnesses : ∀ i : Fin 6,
    RobustTwoMove.Witnesses (lower (i.val+16)) (upper (i.val+16)) := by
  intro ⟨v,hv⟩
  change RobustTwoMove.Witnesses (lower (v+16)) (upper (v+16))
  have cases : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact witnesses16
  · exact witnesses17
  · exact witnesses18
  · exact witnesses19
  · exact witnesses20
  · exact witnesses21

theorem every_intermediate_actual_delivery (i : Fin 6)
    (G : Graph (Fin (i.val+16)))
    (contains : RobustTwoMove.Subgraph (lower (i.val+16)) G)
    (contained : RobustTwoMove.Subgraph G (upper (i.val+16)))
    {s t c : Fin (i.val+16)} (initial : c ≠ s)
    (cop : PursuerPolicy (Fin (i.val+16))) (legal : LegalPursuer G cop)
    (history : History (Fin (i.val+16))) :
    play G t cop 2 history s c = .delivered := by
  exact RobustTwoMove.envelope_actual_delivery contains contained
    (witnesses i) initial cop legal history

def allPairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun s => (List.finRange n).map fun t => (s,t)

/-- The compact row masks are exactly the displayed finite arc lists. -/
theorem masks_match_lists : ∀ i : Fin 6, ∀ s t : Fin (i.val+16),
    ((baseMask (i.val+16) s.val).testBit t.val = true ↔
      (s.val,t.val) ∈ baseMissing (i.val+16)) ∧
    ((fullMask (i.val+16) s.val).testBit t.val = true ↔
      (s.val,t.val) ∈ baseMissing (i.val+16) ++ optionalMissing (i.val+16)) := by
  decide +kernel

theorem exact_endpoint_counts : ∀ i : Fin 6,
    let n := i.val+16
    (allPairs n |>.filter fun p => decide (lower n p.1 p.2)).length = n*(n-1)-3*n ∧
    (allPairs n |>.filter fun p => decide (upper n p.1 p.2)).length = n*(n-1)-2*n := by
  decide +kernel

#print axioms masks_match_lists
#print axioms witnesses
#print axioms every_intermediate_actual_delivery
#print axioms exact_endpoint_counts
end Delivery.SmallDenseEnvelopes
