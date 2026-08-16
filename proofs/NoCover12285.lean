import Erdos7.Capacity
import Erdos7.Certificate12285
import Erdos7.FourForcedPrimeCertificate

/-! Structural exclusion of the second upstream straggler 12285. -/

set_option maxRecDepth 120000

private theorem residual_capacity_12285 :
    ∑ d ∈ remainingAfterFour 12285 3 5 7 13,
      fourPrimeCap 12285 3 5 7 13 d < 5184 := by
  decide

theorem no_distinct_divisor_cover_12285
    (S : Finset (ℕ × ℕ))
    (hdvd : ∀ q ∈ S, q.1 ∣ 12285)
    (hone : ∀ q ∈ S, 1 < q.1)
    (hres : ∀ q ∈ S, q.2 < q.1)
    (hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)))
    (hcov : ∀ x < 12285, ∃ q ∈ S, x % q.1 = q.2) : False := by
  classical
  obtain ⟨h3, h5, h7, h13⟩ := forced_primes_12285 S hdvd hone hres hinj hcov
  obtain ⟨q3, hq3S, hq3mod⟩ := h3
  obtain ⟨q5, hq5S, hq5mod⟩ := h5
  obtain ⟨q7, hq7S, hq7mod⟩ := h7
  obtain ⟨q13, hq13S, hq13mod⟩ := h13
  let U : Finset (ℕ × ℕ) := {q3,q5,q7,q13}
  have hlow : 5184 ≤ (multiCore 12285 U).card := by
    have hUcop : ∀ p ∈ U, ∀ q ∈ U, p ≠ q → Nat.Coprime p.1 q.1 := by
      intro p hp q hq hpq
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hp with rfl | rfl | rfl | rfl <;>
        rcases hq with rfl | rfl | rfl | rfl
      all_goals try { exact absurd rfl hpq }
      all_goals simp only [hq3mod, hq5mod, hq7mod, hq13mod] <;> norm_num
    have hfloor := uncovered_card_ge U
      (by
        intro q hq
        simp only [U, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact hdvd q3 hq3S
        · exact hdvd q5 hq5S
        · exact hdvd q7 hq7S
        · exact hdvd q13 hq13S)
      (by
        intro q hq
        simp only [U, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact hone q3 hq3S
        · exact hone q5 hq5S
        · exact hone q7 hq7S
        · exact hone q13 hq13S)
      hUcop
    have hmods :
        (∏ q ∈ U, q.1) = 3 * 5 * 7 * 13 ∧
        (∏ q ∈ U, (q.1 - 1)) = (3 - 1) * (5 - 1) * (7 - 1) * (13 - 1) := by
      simp [U, hq3mod, hq5mod, hq7mod, hq13mod]
    rcases hmods with ⟨hprod, hminus⟩
    rw [hprod, hminus] at hfloor
    norm_num at hfloor ⊢
    exact hfloor
  exact no_cover_of_four_forced_primes S q3 q5 q7 q13
    (by norm_num) hdvd hone hres hinj hcov
    hq3S hq5S hq7S hq13S
    hq3mod hq5mod hq7mod hq13mod
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [U]) residual_capacity_12285
