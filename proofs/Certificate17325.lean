import Erdos7.ForcedModulus
import Erdos7.ConditionedForcing

/-! Forced-prime certificate for 17325 = 3^2 * 5^2 * 7 * 11. -/

private def allowed17325 : Finset ℕ := (17325 : ℕ).divisors.erase 1

private theorem allowed_of_hyp_17325 (S : Finset (ℕ × ℕ))
    (hdvd : ∀ q ∈ S, q.1 ∣ 17325) (hone : ∀ q ∈ S, 1 < q.1) :
    ∀ q ∈ S, q.1 ∈ allowed17325 := by
  intro q hq
  rw [allowed17325, Finset.mem_erase, Nat.mem_divisors]
  exact ⟨(hone q hq).ne', hdvd q hq, by norm_num⟩

set_option maxRecDepth 150000

private theorem cap_without3_17325 :
    ∑ d ∈ (allowed17325.erase 3), 17325 / d < 17325 := by
  decide

private theorem cap3_without5_17325 :
    ∑ d ∈ (allowed17325.erase 3).erase 5, onePrimeCap 17325 3 d <
      (17325 / 3) * (3 - 1) := by
  decide

private theorem cap3_without7_17325 :
    ∑ d ∈ (allowed17325.erase 3).erase 7, onePrimeCap 17325 3 d <
      (17325 / 3) * (3 - 1) := by
  decide

private theorem cap3_without11_17325 :
    ∑ d ∈ (allowed17325.erase 3).erase 11, onePrimeCap 17325 3 d <
      (17325 / 3) * (3 - 1) := by
  decide

theorem forced_primes_17325
    (S : Finset (ℕ × ℕ))
    (hdvd : ∀ q ∈ S, q.1 ∣ 17325)
    (hone : ∀ q ∈ S, 1 < q.1)
    (hres : ∀ q ∈ S, q.2 < q.1)
    (hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)))
    (hcov : ∀ x < 17325, ∃ q ∈ S, x % q.1 = q.2) :
    (∃ q ∈ S, q.1 = 3) ∧ (∃ q ∈ S, q.1 = 5) ∧
      (∃ q ∈ S, q.1 = 7) ∧ (∃ q ∈ S, q.1 = 11) := by
  have hallowed := allowed_of_hyp_17325 S hdvd hone
  obtain ⟨q3, hq3S, hq3mod⟩ :=
    forced_modulus_of_density S allowed17325 hdvd hinj hcov hallowed cap_without3_17325
  have hq3res : q3.2 < 3 := by simpa [hq3mod] using hres q3 hq3S
  have h5 : ∃ q ∈ S, q.1 = 5 :=
    forced_modulus_after_one_prime S allowed17325 q3 hq3S hq3mod hq3res
      (by norm_num) (by norm_num) (by norm_num) hdvd hinj hcov hallowed cap3_without5_17325
  have h7 : ∃ q ∈ S, q.1 = 7 :=
    forced_modulus_after_one_prime S allowed17325 q3 hq3S hq3mod hq3res
      (by norm_num) (by norm_num) (by norm_num) hdvd hinj hcov hallowed cap3_without7_17325
  have h11 : ∃ q ∈ S, q.1 = 11 :=
    forced_modulus_after_one_prime S allowed17325 q3 hq3S hq3mod hq3res
      (by norm_num) (by norm_num) (by norm_num) hdvd hinj hcov hallowed cap3_without11_17325
  exact ⟨⟨q3, hq3S, hq3mod⟩, h5, h7, h11⟩
