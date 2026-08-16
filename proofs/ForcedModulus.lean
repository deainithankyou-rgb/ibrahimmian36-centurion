import Erdos7.Density

/-!
A generic forced-modulus rule derived from the ordinary density bound.
The finite arithmetic set `Allowed` is an untrusted-search output; Lean only
checks subset membership and the final strict capacity inequality.
-/

theorem forced_modulus_of_density
    {N d0 : ℕ} (S : Finset (ℕ × ℕ)) (Allowed : Finset ℕ)
    (hdvd : ∀ q ∈ S, q.1 ∣ N)
    (hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)))
    (hcov : ∀ x < N, ∃ q ∈ S, x % q.1 = q.2)
    (hallowed : ∀ q ∈ S, q.1 ∈ Allowed)
    (harith : ∑ d ∈ Allowed.erase d0, N / d < N) :
    ∃ q ∈ S, q.1 = d0 := by
  by_contra hno
  push_neg at hno
  have hkey : N ≤ ∑ q ∈ S, N / q.1 :=
    covering_density N S hdvd hcov
  have hsumD : ∑ d ∈ S.image Prod.fst, N / d = ∑ q ∈ S, N / q.1 :=
    Finset.sum_image hinj
  have hsub : S.image Prod.fst ⊆ Allowed.erase d0 := by
    intro d hd
    obtain ⟨q, hqS, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_erase.mpr ⟨hno q hqS, hallowed q hqS⟩
  have hmono : ∑ d ∈ S.image Prod.fst, N / d ≤
      ∑ d ∈ Allowed.erase d0, N / d :=
    Finset.sum_le_sum_of_subset hsub
  rw [hsumD] at hmono
  omega

/-- Closed kernel arithmetic for the first 10395 forcing step. -/
theorem capacity_without_3_10395 :
    ∑ d ∈ ((10395 : ℕ).divisors.erase 1).erase 3, 10395 / d < 10395 := by
  norm_num [Nat.divisors]
