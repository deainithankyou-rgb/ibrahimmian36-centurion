import Mathlib

/-!
A local overlap-charging rule for certified forest witnesses.
If `P` is already contained in the covered region `B`, then when a new
finite set `A` is added, at least `A ∩ P` is duplicate coverage.
This rule can be iterated in a topological order of any forest witness.
-/

theorem card_union_le_card_add_sub_parent_inter
    {α : Type*} [DecidableEq α]
    (A B P : Finset α) (hPB : P ⊆ B) :
    (B ∪ A).card ≤ B.card + A.card - (A ∩ P).card := by
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
  omega

/-- Exact two-set inclusion-exclusion, exposed as the base overlap rule. -/
theorem card_union_eq_card_add_sub_inter
    {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∪ B).card = A.card + B.card - (A ∩ B).card := by
  exact Finset.card_union A B
