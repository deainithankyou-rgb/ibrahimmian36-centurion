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
  rcases q3 with ⟨d3, a3⟩
  rcases q5 with ⟨d5, a5⟩
  rcases q7 with ⟨d7, a7⟩
  rcases q11 with ⟨d11, a11⟩
  simp only at hq3mod hq5mod hq7mod hq11mod
  subst d3
  subst d5
  subst d7
  subst d11
  let U : Finset (ℕ × ℕ) := {(3,a3), (5,a5), (7,a7), (11,a11)}
  have hlow : 7200 ≤ (multiCore 17325 U).card := by
    have h := uncovered_card_ge (N := 17325) U
      (by
        intro p hp
        simp only [U, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num)
      (by
        intro p hp
        simp only [U, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num)
      (by
        intro p hp q hq hpq
        simp only [U, Finset.mem_insert, Finset.mem_singleton] at hp hq
        rcases hp with rfl | rfl | rfl | rfl <;>
          rcases hq with rfl | rfl | rfl | rfl <;>
          (try contradiction) <;> norm_num)
    simpa [multiCore, U] using h
  exact no_cover_of_four_forced_primes S (3,a3) (5,a5) (7,a7) (11,a11)
    (by norm_num) hdvd hone hres hinj hcov
    hq3S hq5S hq7S hq11S
    rfl rfl rfl rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [U]) residual_capacity_17325
