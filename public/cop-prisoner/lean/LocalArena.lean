import FiniteGame

/-! Local asymmetric arenas, safe transfer, and projection into the actual
game. Local messenger and cop states may differ, including an outside cop
state. Safe goals are reached after the intervening cop reply; delivery goals
are terminal immediately before collision. No geometric projection or finite
certificate family is asserted by this generic semantic kernel. -/
namespace Delivery.LocalArena
open FiniteGame

/-- A finite strategy that ends safely at the start of a messenger turn.
Unlike Winning, reaching the goal does not waive a collision check. -/
inductive SafeReach {V : Type} (E : Graph V) (Goal : V → Prop) : Nat → V → V → Prop
  | done {k r c} : Goal r → r ≠ c → SafeReach E Goal k r c
  | step {k r c z} : r ≠ c → Legal E r z → z ≠ c →
      (∀ c', Legal E c c' → z ≠ c') →
      (∀ c', Legal E c c' → SafeReach E Goal k z c') →
      SafeReach E Goal (k+1) r c

theorem safe_mono {V : Type} {E : Graph V} {Goal : V → Prop} {r c : V} {k l : Nat}
    (reach : SafeReach E Goal k r c) (bound : k ≤ l) : SafeReach E Goal l r c := by
  induction reach generalizing l with
  | done goal safe => exact SafeReach.done goal safe
  | @step k r c z distinct move safeNow safeReply next ih =>
    cases l with
    | zero => omega
    | succ l =>
      exact SafeReach.step distinct move safeNow safeReply
        (fun c' reply => ih c' reply (by omega))

theorem safe_compose {V : Type} {E : Graph V} {P Q : V → Prop} {r c : V} {a b : Nat}
    (first : SafeReach E P a r c)
    (next : ∀ z d, P z → z ≠ d → SafeReach E Q b z d) : SafeReach E Q (a+b) r c := by
  induction first with
  | @done k r c goal safe => exact safe_mono (next r c goal safe) (by omega)
  | @step k r c z distinct move safeNow safeReply children ih =>
    have result := SafeReach.step distinct move safeNow safeReply ih
    simpa only [Nat.add_assoc,Nat.add_comm 1 b] using result

theorem safe_then_delivery {V : Type} {E : Graph V} {P : V → Prop} {t r c : V} {a b : Nat}
    (first : SafeReach E P a r c)
    (next : ∀ z d, P z → z ≠ d → Winning E t b z d) : Winning E t (a+b) r c := by
  induction first with
  | @done k r c goal safe => exact winning_mono (next r c goal safe) (by omega)
  | @step k r c z distinct move safeNow safeReply children ih =>
    have result := Winning.step distinct move safeNow safeReply ih
    simpa only [Nat.add_assoc,Nat.add_comm 1 b] using result

/-- A sequence of transfers, retaining the cop response between every pair
of stages. Stage predicates may be columns, windows, or arbitrary safe sets. -/
theorem safe_chain {V : Type} {E : Graph V} (P : Nat → V → Prop) (τ : Nat)
    (transfer : ∀ i r c, P i r → r ≠ c → SafeReach E (P (i+1)) τ r c)
    (j : Nat) {r c : V} (start : P 0 r) (safe : r ≠ c) :
    SafeReach E (P j) (j*τ) r c := by
  induction j with
  | zero => exact SafeReach.done start safe
  | succ j ih =>
    have result := safe_compose ih (transfer j)
    simpa only [Nat.succ_mul] using result

structure Arena (R C : Type) where
  messenger : R → R → Prop
  pursuer : C → C → Prop
  collision : R → C → Prop

/-- The local messenger is embedded, while all actual cop moves project to
allowed local replies. Only reflection of actual collision is required. -/
structure Simulation {V R C : Type} (E : Graph V) (A : Arena R C) where
  embed : R → V
  project : V → C
  messenger_sound : ∀ r z, A.messenger r z → Legal E (embed r) (embed z)
  pursuer_complete : ∀ c d, Legal E c d → A.pursuer (project c) (project d)
  collision_complete : ∀ r c, embed r=c → A.collision r (project c)

structure Data (R C : Type) where
  region : R → C → Prop
  rank : R → C → Nat
  move : R → C → R

structure SafeChecked {R C : Type} (A : Arena R C) (Goal : R → Prop) (D : Data R C) : Prop where
  valid : ∀ r c, D.region r c →
    (Goal r ∧ ¬ A.collision r c) ∨
    (0 < D.rank r c ∧ ¬ A.collision r c ∧ A.messenger r (D.move r c) ∧
      ¬ A.collision (D.move r c) c ∧
      ∀ c', A.pursuer c c' → ¬ A.collision (D.move r c) c' ∧
        D.region (D.move r c) c' ∧ D.rank (D.move r c) c' < D.rank r c)

structure DeliveryChecked {R C : Type} (A : Arena R C) (Goal : R → Prop) (D : Data R C) : Prop where
  valid : ∀ r c, D.region r c → Goal r ∨
    (0 < D.rank r c ∧ ¬ A.collision r c ∧ A.messenger r (D.move r c) ∧
      (Goal (D.move r c) ∨ (¬ A.collision (D.move r c) c ∧
      ∀ c', A.pursuer c c' → ¬ A.collision (D.move r c) c' ∧
        D.region (D.move r c) c' ∧ D.rank (D.move r c) c' < D.rank r c)))

/-- A checked safe-transfer certificate projects to the actual alternating
game with its exact supplied rank, including all waits and all cop replies. -/
theorem safe_projection {V R C : Type} {E : Graph V} {A : Arena R C}
    {Goal : R → Prop} {P : V → Prop} {D : Data R C}
    (sim : Simulation E A) (checked : SafeChecked A Goal D)
    (goal_sound : ∀ r, Goal r → P (sim.embed r)) (r : R) (c : V)
    (inside : D.region r (sim.project c)) :
    SafeReach E P (D.rank r (sim.project c)) (sim.embed r) c := by
  generalize rankEq : D.rank r (sim.project c)=k
  induction k using Nat.strongRecOn generalizing r c with
  | ind k ih =>
    obtain goal | ⟨positive,distinct,move,safeNow,future⟩ := checked.valid r (sim.project c) inside
    · exact SafeReach.done (goal_sound r goal.1)
        (fun same => goal.2 (sim.collision_complete r c same))
    · cases k with
      | zero => omega
      | succ k =>
        apply SafeReach.step (z := sim.embed (D.move r (sim.project c)))
          (fun same => distinct (sim.collision_complete r c same))
          (sim.messenger_sound _ _ move)
          (fun same => safeNow (sim.collision_complete _ c same))
        · intro c' reply same
          exact (future (sim.project c') (sim.pursuer_complete c c' reply)).1
            (sim.collision_complete _ c' same)
        · intro c' reply
          have next := future (sim.project c') (sim.pursuer_complete c c' reply)
          have child := ih (D.rank (D.move r (sim.project c)) (sim.project c')) (by omega)
            (D.move r (sim.project c)) c' next.2.1 rfl
          exact safe_mono child (by omega)

/-- Delivery goals identify the actual recipient. Arrival is terminal before
collision, whereas every nonterminal local move pays for the cop reply. -/
theorem delivery_projection {V R C : Type} {E : Graph V} {A : Arena R C}
    {Goal : R → Prop} {t : V} {D : Data R C}
    (sim : Simulation E A) (checked : DeliveryChecked A Goal D)
    (goal_sound : ∀ r, Goal r → sim.embed r=t) (r : R) (c : V)
    (inside : D.region r (sim.project c)) :
    Winning E t (D.rank r (sim.project c)) (sim.embed r) c := by
  generalize rankEq : D.rank r (sim.project c)=k
  induction k using Nat.strongRecOn generalizing r c with
  | ind k ih =>
    obtain goal | ⟨positive,distinct,move,finish | ⟨safeNow,future⟩⟩ :=
      checked.valid r (sim.project c) inside
    · rw [goal_sound r goal]
      exact Winning.delivered
    · cases k with
      | zero => omega
      | succ k =>
        have legal := sim.messenger_sound _ _ move
        rw [goal_sound _ finish] at legal
        exact Winning.finish (fun same => distinct (sim.collision_complete r c same)) legal
    · cases k with
      | zero => omega
      | succ k =>
        apply Winning.step (z := sim.embed (D.move r (sim.project c)))
          (fun same => distinct (sim.collision_complete r c same))
          (sim.messenger_sound _ _ move)
          (fun same => safeNow (sim.collision_complete _ c same))
        · intro c' reply same
          exact (future (sim.project c') (sim.pursuer_complete c c' reply)).1
            (sim.collision_complete _ c' same)
        · intro c' reply
          have next := future (sim.project c') (sim.pursuer_complete c c' reply)
          have child := ih (D.rank (D.move r (sim.project c)) (sim.project c')) (by omega)
            (D.move r (sim.project c)) c' next.2.1 rfl
          exact winning_mono child (by omega)

theorem transfer_then_delivery {V : Type} {E : Graph V} (P : Nat → V → Prop)
    (τ D : Nat) (t : V)
    (transfer : ∀ i r c, P i r → r ≠ c → SafeReach E (P (i+1)) τ r c)
    (j : Nat) (delivery : ∀ r c, P j r → r ≠ c → Winning E t D r c)
    {r c : V} (start : P 0 r) (safe : r ≠ c) : Winning E t (j*τ+D) r c :=
  safe_then_delivery (safe_chain P τ transfer j start safe) delivery

#print axioms safe_projection
#print axioms delivery_projection
#print axioms transfer_then_delivery
end Delivery.LocalArena
