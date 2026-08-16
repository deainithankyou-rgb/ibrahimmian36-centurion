import Mathlib

/-!
Generic trusted logic for capacity certificates.
The problem-specific layer only has to provide finite contribution sets `A i`
and certified cardinality upper bounds `cap i`.
-/

/-- A finite cover cannot use more points than the sum of certified capacities. -/
theorem cover_card_le_sum_capacity
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (Selected : Finset ι)
    (A : ι → Finset α) (cap : ι → ℕ)
    (hcover : U ⊆ Selected.biUnion A)
    (hcap : ∀ i ∈ Selected, (A i).card ≤ cap i) :
    U.card ≤ ∑ i ∈ Selected, cap i := by
  calc
    U.card ≤ (Selected.biUnion A).card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ Selected, (A i).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ Selected, cap i := Finset.sum_le_sum fun i hi => hcap i hi

/-- If even every allowed contribution together has insufficient capacity,
no selected subfamily can cover the target core. -/
theorem no_cover_of_total_capacity
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (Allowed Selected : Finset ι)
    (A : ι → Finset α) (cap : ι → ℕ)
    (hsel : Selected ⊆ Allowed)
    (hcover : U ⊆ Selected.biUnion A)
    (hcap : ∀ i ∈ Selected, (A i).card ≤ cap i)
    (harith : ∑ i ∈ Allowed, cap i < U.card) : False := by
  have hcovered := cover_card_le_sum_capacity U Selected A cap hcover hcap
  have hsum : ∑ i ∈ Selected, cap i ≤ ∑ i ∈ Allowed, cap i :=
    Finset.sum_le_sum_of_subset hsel
  omega

/-- Forced-index rule.  If removing candidate `d` from the allowed family
makes total capacity smaller than the target core, every covering selected
subfamily must contain `d`. -/
theorem forced_index_of_capacity
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (Allowed Selected : Finset ι) (d : ι)
    (A : ι → Finset α) (cap : ι → ℕ)
    (hsel : Selected ⊆ Allowed)
    (hcover : U ⊆ Selected.biUnion A)
    (hcap : ∀ i ∈ Selected, (A i).card ≤ cap i)
    (harith : ∑ i ∈ Allowed.erase d, cap i < U.card) :
    d ∈ Selected := by
  by_contra hd
  have hsel' : Selected ⊆ Allowed.erase d := by
    intro i hi
    exact Finset.mem_erase.mpr ⟨by
      intro hid
      subst i
      exact hd hi, hsel hi⟩
  exact no_cover_of_total_capacity U (Allowed.erase d) Selected A cap
    hsel' hcover hcap harith
