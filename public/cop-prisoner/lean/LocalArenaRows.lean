import LocalArena

/-! Sparse reply-list checking for local certificates. A proved coverage
condition, rather than a search procedure, justifies checking only the listed
cop replies. Extra listed replies are harmless. -/
namespace Delivery.LocalArenaRows
open LocalArena

def repliesGood {R C : Type} (A : Arena R C) (D : Data R C)
    [DecidableRel A.collision] [DecidableRel D.region]
    (z : R) (rank : Nat) (replies : List C) : Bool :=
  replies.all fun c' => decide (¬ A.collision z c' ∧ D.region z c' ∧ D.rank z c' < rank)

theorem replies_good {R C : Type} (A : Arena R C) (D : Data R C)
    [DecidableRel A.collision] [DecidableRel D.region]
    (z : R) (rank : Nat) (replies : List C)
    (check : repliesGood A D z rank replies=true) {c' : C} (member : c' ∈ replies) :
    ¬ A.collision z c' ∧ D.region z c' ∧ D.rank z c' < rank :=
  of_decide_eq_true ((List.all_eq_true.mp check) c' member)

def SafeRowCondition {R C : Type} (A : Arena R C) (Goal : R → Prop) (D : Data R C)
    [DecidableRel A.collision] [DecidableRel D.region]
    (replies : C → List C) (r : R) (c : C) : Prop :=
  D.region r c → (Goal r ∧ ¬ A.collision r c) ∨
    (0 < D.rank r c ∧ ¬ A.collision r c ∧ A.messenger r (D.move r c) ∧
      ¬ A.collision (D.move r c) c ∧
      repliesGood A D (D.move r c) (D.rank r c) (replies c)=true)

theorem safe_checked {R C : Type} (A : Arena R C) (Goal : R → Prop) (D : Data R C)
    [DecidableRel A.collision] [DecidableRel D.region]
    (replies : C → List C)
    (complete : ∀ c c', A.pursuer c c' → c' ∈ replies c)
    (check : ∀ r c, SafeRowCondition A Goal D replies r c) : SafeChecked A Goal D := by
  constructor
  intro r c inside
  obtain goal | ⟨positive,distinct,move,safeNow,future⟩ := check r c inside
  · exact Or.inl goal
  · exact Or.inr ⟨positive,distinct,move,safeNow,fun c' legal =>
      replies_good A D _ _ _ future (complete c c' legal)⟩

def DeliveryRowCondition {R C : Type} (A : Arena R C) (Goal : R → Prop) (D : Data R C)
    [DecidableRel A.collision] [DecidableRel D.region]
    (replies : C → List C) (r : R) (c : C) : Prop :=
  D.region r c → Goal r ∨
    (0 < D.rank r c ∧ ¬ A.collision r c ∧ A.messenger r (D.move r c) ∧
      (Goal (D.move r c) ∨ (¬ A.collision (D.move r c) c ∧
      repliesGood A D (D.move r c) (D.rank r c) (replies c)=true)))

theorem delivery_checked {R C : Type} (A : Arena R C) (Goal : R → Prop) (D : Data R C)
    [DecidableRel A.collision] [DecidableRel D.region]
    (replies : C → List C)
    (complete : ∀ c c', A.pursuer c c' → c' ∈ replies c)
    (check : ∀ r c, DeliveryRowCondition A Goal D replies r c) : DeliveryChecked A Goal D := by
  constructor
  intro r c inside
  obtain goal | ⟨positive,distinct,move,finish | ⟨safeNow,future⟩⟩ := check r c inside
  · exact Or.inl goal
  · exact Or.inr ⟨positive,distinct,move,Or.inl finish⟩
  · exact Or.inr ⟨positive,distinct,move,Or.inr ⟨safeNow,fun c' legal =>
      replies_good A D _ _ _ future (complete c c' legal)⟩⟩

#print axioms safe_checked
#print axioms delivery_checked
end Delivery.LocalArenaRows
