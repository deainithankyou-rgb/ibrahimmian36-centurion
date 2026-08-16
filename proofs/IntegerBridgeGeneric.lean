import Mathlib

/-!
Generic bridge from an integer covering to one finite normalized period.
A problem-specific finite exclusion theorem can be plugged into this bridge.
-/

theorem integer_cover_excluded_by_finite
    {N : ℕ}
    (finite_exclusion : ∀ S : Finset (ℕ × ℕ),
      (∀ q ∈ S, q.1 ∣ N) →
      (∀ q ∈ S, 1 < q.1) →
      (∀ q ∈ S, q.2 < q.1) →
      Set.InjOn Prod.fst (S : Set (ℕ × ℕ)) →
      (∀ x < N, ∃ q ∈ S, x % q.1 = q.2) → False)
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ N := by
  classical
  intro hlcm
  have hdvdN : ∀ i, n i ∣ N :=
    fun i => dvd_trans (Finset.dvd_lcm (Finset.mem_univ i)) hlcm
  set r : ι → ℕ := fun i => ((a i) % (n i : ℤ)).toNat with hrdef
  set S : Finset (ℕ × ℕ) := Finset.univ.image (fun i => (n i, r i)) with hSdef
  have hdvd : ∀ p ∈ S, p.1 ∣ N := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact hdvdN i
  have hone : ∀ p ∈ S, 1 < p.1 := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact hgt i
  have hres : ∀ p ∈ S, p.2 < p.1 := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    change r i < n i
    rw [hrdef]
    have hnposNat : 0 < n i := lt_trans Nat.zero_lt_one (hgt i)
    have hnpos : (0 : ℤ) < (n i : ℤ) := by exact_mod_cast hnposNat
    have hnonneg : 0 ≤ (a i) % (n i : ℤ) :=
      Int.emod_nonneg (a i) (ne_of_gt hnpos)
    exact (Int.toNat_lt hnonneg).2 (Int.emod_lt_of_pos (a i) hnpos)
  have hinjS : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)) := by
    intro p hp q hq hfst
    rw [Finset.mem_coe, hSdef, Finset.mem_image] at hp hq
    obtain ⟨i, -, rfl⟩ := hp
    obtain ⟨j, -, rfl⟩ := hq
    have hij : i = j := hinj hfst
    rw [hij]
  have hcov' : ∀ x < N, ∃ p ∈ S, x % p.1 = p.2 := by
    intro x _
    obtain ⟨i, hi⟩ := hcov (x : ℤ)
    refine ⟨(n i, r i), Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩, ?_⟩
    have h1 : (a i) % (n i : ℤ) = (x : ℤ) % (n i : ℤ) :=
      Int.modEq_iff_dvd.mpr hi
    have h2 : ((x : ℤ)) % (n i : ℤ) = ((x % n i : ℕ) : ℤ) := by
      rw [Int.natCast_mod]
    change x % n i = r i
    rw [hrdef]
    simp only [h1, h2, Int.toNat_natCast]
  exact finite_exclusion S hdvd hone hres hinjS hcov'
