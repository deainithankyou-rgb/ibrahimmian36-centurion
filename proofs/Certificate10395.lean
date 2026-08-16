import Erdos7.ForcedModulus
import Erdos7.ConditionedForcing

/-! First concrete certificate beyond the upstream capacity straggler 10395. -/

private def allowed10395 : Finset ℕ := (10395 : ℕ).divisors.erase 1

private theorem allowed_of_hyp_10395 (S : Finset (ℕ × ℕ))
    (hdvd : ∀ q ∈ S, q.1 ∣ 10395) (hone : ∀ q ∈ S, 1 < q.1) :
    ∀ q ∈ S, q.1 ∈ allowed10395 := by
  intro q hq
  rw [allowed10395, Finset.mem_erase, Nat.mem_divisors]
  exact ⟨(hone q hq).ne', hdvd q hq, by norm_num⟩

private theorem cap3_without5 :
    ∑ d ∈ (allowed10395.erase 3).erase 5, onePrimeCap 10395 3 d <
      (10395 / 3) * (3 - 1) := by
  norm_num [allowed10395, onePrimeCap, Nat.divisors]

private theorem cap3_without7 :
    ∑ d ∈ (allowed10395.erase 3).erase 7, onePrimeCap 10395 3 d <
      (10395 / 3) * (3 - 1) := by
  norm_num [allowed10395, onePrimeCap, Nat.divisors]

private theorem cap3_without11 :
    ∑ d ∈ (allowed10395.erase 3).erase 11, onePrimeCap 10395 3 d <
      (10395 / 3) * (3 - 1) := by
  norm_num [allowed10395, onePrimeCap, Nat.divisors]

/-- Any normalized distinct-modulus covering of `[0,10395)` using divisors of
10395 would have to contain classes with moduli 3, 5, 7 and 11. -/
theorem forced_primes_10395
    (S : Finset (ℕ × ℕ))
    (hdvd : ∀ q ∈ S, q.1 ∣ 10395)
    (hone : ∀ q ∈ S, 1 < q.1)
    (hres : ∀ q ∈ S, q.2 < q.1)
    (hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)))
    (hcov : ∀ x < 10395, ∃ q ∈ S, x % q.1 = q.2) :
    (∃ q ∈ S, q.1 = 3) ∧ (∃ q ∈ S, q.1 = 5) ∧
      (∃ q ∈ S, q.1 = 7) ∧ (∃ q ∈ S, q.1 = 11) := by
  have hallowed := allowed_of_hyp_10395 S hdvd hone
  obtain ⟨q3, hq3S, hq3mod⟩ :=
    forced_modulus_of_density S allowed10395 hdvd hinj hcov hallowed capacity_without_3_10395
  have hq3res : q3.2 < 3 := by simpa [hq3mod] using hres q3 hq3S
  have h5 : ∃ q ∈ S, q.1 = 5 :=
    forced_modulus_after_one_prime S allowed10395 q3 hq3S hq3mod hq3res
      (by norm_num) (by norm_num) (by norm_num) hdvd hinj hcov hallowed cap3_without5
  have h7 : ∃ q ∈ S, q.1 = 7 :=
    forced_modulus_after_one_prime S allowed10395 q3 hq3S hq3mod hq3res
      (by norm_num) (by norm_num) (by norm_num) hdvd hinj hcov hallowed cap3_without7
  have h11 : ∃ q ∈ S, q.1 = 11 :=
    forced_modulus_after_one_prime S allowed10395 q3 hq3S hq3mod hq3res
      (by norm_num) (by norm_num) (by norm_num) hdvd hinj hcov hallowed cap3_without11
  exact ⟨⟨q3, hq3S, hq3mod⟩, h5, h7, h11⟩
