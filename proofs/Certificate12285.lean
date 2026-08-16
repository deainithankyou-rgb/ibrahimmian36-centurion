import Erdos7.ForcedModulus
import Erdos7.ConditionedForcing

/-! Forced-prime certificate for 12285 = 3^3 * 5 * 7 * 13. -/

private def allowed12285 : Finset ℕ := (12285 : ℕ).divisors.erase 1

private theorem allowed_of_hyp_12285 (S : Finset (ℕ × ℕ))
    (hdvd : ∀ q ∈ S, q.1 ∣ 12285) (hone : ∀ q ∈ S, 1 < q.1) :
    ∀ q ∈ S, q.1 ∈ allowed12285 := by
  intro q hq
  rw [allowed12285, Finset.mem_erase, Nat.mem_divisors]
  exact ⟨(hone q hq).ne', hdvd q hq, by norm_num⟩

set_option maxRecDepth 120000

private theorem cap_without3_12285 :
    ∑ d ∈ (allowed12285.erase 3), 12285 / d < 12285 := by
  decide

private theorem cap3_without5_12285 :
    ∑ d ∈ (allowed12285.erase 3).erase 5, onePrimeCap 12285 3 d <
      (12285 / 3) * (3 - 1) := by
  decide

private theorem cap3_without7_12285 :
    ∑ d ∈ (allowed12285.erase 3).erase 7, onePrimeCap 12285 3 d <
      (12285 / 3) * (3 - 1) := by
  decide

private theorem cap3_without13_12285 :
    ∑ d ∈ (allowed12285.erase 3).erase 13, onePrimeCap 12285 3 d <
      (12285 / 3) * (3 - 1) := by
  decide

theorem forced_primes_12285
    (S : Finset (ℕ × ℕ))
    (hdvd : ∀ q ∈ S, q.1 ∣ 12285)
    (hone : ∀ q ∈ S, 1 < q.1)
    (hres : ∀ q ∈ S, q.2 < q.1)
    (hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)))
    (hcov : ∀ x < 12285, ∃ q ∈ S, x % q.1 = q.2) :
    (∃ q ∈ S, q.1 = 3) ∧ (∃ q ∈ S, q.1 = 5) ∧
      (∃ q ∈ S, q.1 = 7) ∧ (∃ q ∈ S, q.1 = 13) := by
  have hallowed := allowed_of_hyp_12285 S hdvd hone
  obtain ⟨q3, hq3S, hq3mod⟩ :=
    forced_modulus_of_density S allowed12285 hdvd hinj hcov hallowed cap_without3_12285
  have hq3res : q3.2 < 3 := by simpa [hq3mod] using hres q3 hq3S
  have h5 : ∃ q ∈ S, q.1 = 5 :=
    forced_modulus_after_one_prime S allowed12285 q3 hq3S hq3mod hq3res
      (by norm_num) (by norm_num) (by norm_num) hdvd hinj hcov hallowed cap3_without5_12285
  have h7 : ∃ q ∈ S, q.1 = 7 :=
    forced_modulus_after_one_prime S allowed12285 q3 hq3S hq3mod hq3res
      (by norm_num) (by norm_num) (by norm_num) hdvd hinj hcov hallowed cap3_without7_12285
  have h13 : ∃ q ∈ S, q.1 = 13 :=
    forced_modulus_after_one_prime S allowed12285 q3 hq3S hq3mod hq3res
      (by norm_num) (by norm_num) (by norm_num) hdvd hinj hcov hallowed cap3_without13_12285
  exact ⟨⟨q3, hq3S, hq3mod⟩, h5, h7, h13⟩
