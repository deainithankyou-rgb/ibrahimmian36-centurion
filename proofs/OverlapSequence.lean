import Mathlib

/-!
A small certificate interpreter for overlap-corrected capacity bounds.
Each step supplies a new contribution set `A` and a parent set `P` already
contained in the current covered region.  This is enough to justify charging
`|A| - |A ∩ P|` new points.  A compiler can topologically order any forest
witness and emit exactly this sequence.
-/

def overlapUnion {α : Type*} [DecidableEq α]
    (B : Finset α) : List (Finset α × Finset α) → Finset α
  | [] => B
  | (A, _) :: xs => overlapUnion (B ∪ A) xs

def overlapValid {α : Type*} [DecidableEq α]
    (B : Finset α) : List (Finset α × Finset α) → Prop
  | [] => True
  | (A, P) :: xs => P ⊆ B ∧ overlapValid (B ∪ A) xs

def overlapCost {α : Type*} [DecidableEq α] :
    List (Finset α × Finset α) → ℕ
  | [] => 0
  | (A, P) :: xs => A.card - (A ∩ P).card + overlapCost xs

/-- Soundness of an ordered overlap certificate. -/
theorem overlap_sequence_card_bound
    {α : Type*} [DecidableEq α]
    (B : Finset α) (xs : List (Finset α × Finset α))
    (hvalid : overlapValid B xs) :
    (overlapUnion B xs).card ≤ B.card + overlapCost xs := by
  induction xs generalizing B with
  | nil => simp [overlapUnion, overlapCost]
  | cons ap xs ih =>
      rcases ap with ⟨A, P⟩
      simp only [overlapValid] at hvalid
      rcases hvalid with ⟨hPB, htail⟩
      have hsub : A ∩ P ⊆ A ∩ B := by
        intro x hx
        simp only [Finset.mem_inter] at hx ⊢
        exact ⟨hx.1, hPB hx.2⟩
      have hcard : (A ∩ P).card ≤ (A ∩ B).card :=
        Finset.card_le_card hsub
      have hIE := Finset.card_union_add_card_inter B A
      have hcomm : (B ∩ A).card = (A ∩ B).card := by
        rw [Finset.inter_comm]
      rw [hcomm] at hIE
      have hstep :
          (B ∪ A).card ≤ B.card + (A.card - (A ∩ P).card) := by
        omega
      have hrest := ih (B := B ∪ A) htail
      change (overlapUnion (B ∪ A) xs).card ≤
        B.card + overlapCost ((A, P) :: xs)
      calc
        (overlapUnion (B ∪ A) xs).card
            ≤ (B ∪ A).card + overlapCost xs := hrest
        _ ≤ (B.card + (A.card - (A ∩ P).card)) + overlapCost xs :=
          Nat.add_le_add_right hstep _
        _ = B.card + overlapCost ((A, P) :: xs) := by
          simp [overlapCost, Nat.add_assoc]
