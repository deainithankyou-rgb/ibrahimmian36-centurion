import Erdos7.Capacity
import Erdos7.Certificate17325
import Erdos7.FourForcedPrimeCertificate

/-! Structural exclusion of the third upstream straggler 17325. -/

set_option maxRecDepth 150000

private theorem residual_capacity_17325 :
    ∑ d ∈ remainingAfterFour 17325 3 5 7 11,
      fourPrimeCap 17325 3 5 7 11 d < 7200 := by
  decide

theorem no_distinct_divisor_cover_17325
    (S : Finset (ℕ × ℕ))
    (hdvd : ∀ q ∈ S, q.1 ∣ 17325)
    (hone : ∀ q ∈ S, 1 < q.1)
    (hres : ∀ q ∈ S, q.2 < q.1)
    (hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)))
    (hcov : ∀ x < 17325, ∃ q ∈ S, x % q.1 = q.2) : False := by
  classical
  obtain ⟨h3, h5, h7, h11⟩ := forced_primes_17325 S hdvd hone hres hinj hcov
  obtain ⟨q3, hq3S, hq3mod⟩ := h3
  obtain ⟨q5, hq5S, hq5mod⟩ := h5
  obtain ⟨q7, hq7S, hq7mod⟩ := h7
  obtain ⟨q11, hq11S, hq11mod⟩ := h11
  let U : Finset (ℕ × ℕ) := {q3,q5,q7,q11}
  have hlow : 7200 ≤ (multiCore 17325 U).card := by
    have hUcop : ∀ p ∈ U, ∀ q ∈ U, p ≠ q → Nat.Coprime p.1 q.1 := by
      intro p hp q hq hpq
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hp with rfl | rfl | rfl | rfl <;>
        rcases hq with rfl | rfl | rfl | rfl
      all_goals try { exact absurd rfl hpq }
      all_goals simp only [hq3mod, hq5mod, hq7mod, hq11mod] <;> norm_num
    have hfloor := uncovered_card_ge U
      (by
        intro q hq
        simp only [U, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact hdvd q3 hq3S
        · exact hdvd q5 hq5S
        · exact hdvd q7 hq7S
        · exact hdvd q11 hq11S)
      (by
        intro q hq
        simp only [U, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact hone q3 hq3S
        · exact hone q5 hq5S
        · exact hone q7 hq7S
        · exact hone q11 hq11S)
      hUcop
    have hmods :
        (∏ q ∈ U, q.1) = 3 * 5 * 7 * 11 ∧
        (∏ q ∈ U, (q.1 - 1)) = (3 - 1) * (5 - 1) * (7 - 1) * (11 - 1) := by
      simp [U, hq3mod, hq5mod, hq7mod, hq11mod]
    rcases hmods with ⟨hprod, hminus⟩
    rw [hprod, hminus] at hfloor
    norm_num at hfloor ⊢
    exact hfloor
  exact no_cover_of_four_forced_primes S q3 q5 q7 q11
    (by norm_num) hdvd hone hres hinj hcov
    hq3S hq5S hq7S hq11S
    hq3mod hq5mod hq7mod hq11mod
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [U]) residual_capacity_17325
