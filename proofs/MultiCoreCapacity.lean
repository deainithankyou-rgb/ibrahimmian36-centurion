import Erdos7.ConditionedForcing

/-!
Generic residual-core layer for a finite set of already selected classes.
-/

def multiCore (N : ℕ) (U : Finset (ℕ × ℕ)) : Finset ℕ :=
  (Finset.range N).filter (fun x => ∀ p ∈ U, x % p.1 ≠ p.2)

def multiCoreClass (N : ℕ) (U : Finset (ℕ × ℕ)) (q : ℕ × ℕ) : Finset ℕ :=
  (multiCore N U).filter (fun x => x % q.1 = q.2)

/-- Removing all already selected classes still leaves a cover of their
residual core. -/
theorem multiCore_covered_by_residual
    {N : ℕ} (S U : Finset (ℕ × ℕ))
    (hUS : U ⊆ S)
    (hcov : ∀ x < N, ∃ q ∈ S, x % q.1 = q.2) :
    multiCore N U ⊆ (S \ U).biUnion (multiCoreClass N U) := by
  classical
  intro x hx
  simp only [multiCore, Finset.mem_filter, Finset.mem_range] at hx
  obtain ⟨q, hqS, hqx⟩ := hcov x hx.1
  have hqnotU : q ∉ U := by
    intro hqU
    exact hx.2 q hqU hqx
  apply Finset.mem_biUnion.mpr
  refine ⟨q, Finset.mem_sdiff.mpr ⟨hqS, hqnotU⟩, ?_⟩
  simp only [multiCoreClass, Finset.mem_filter]
  exact ⟨by
    simp only [multiCore, Finset.mem_filter, Finset.mem_range]
    exact hx, hqx⟩

/-- A class restricted to a multi-core is no larger than its one-prime bound
for any selected prime class in the core certificate. -/
theorem multiCoreClass_card_le_onePrime
    {N : ℕ} (U : Finset (ℕ × ℕ)) (p q : ℕ × ℕ)
    (hpU : p ∈ U)
    (hpprime : p.1.Prime) (hpdvd : p.1 ∣ N)
    (hpres : p.2 < p.1) (hqdvd : q.1 ∣ N) :
    (multiCoreClass N U q).card ≤ onePrimeCap N p.1 q.1 := by
  classical
  have hsub : multiCoreClass N U q ⊆ conditionedClass N p q := by
    intro x hx
    simp only [multiCoreClass, Finset.mem_filter] at hx
    rcases hx with ⟨hxcore, hxq⟩
    simp only [multiCore, Finset.mem_filter, Finset.mem_range] at hxcore
    simp only [conditionedClass, Finset.mem_filter, Finset.mem_range]
    exact ⟨hxcore.1, hxq, hxcore.2 p hpU⟩
  exact (Finset.card_le_card hsub).trans
    (conditionedClass_card_le p q hpprime hpdvd hpres hqdvd)
