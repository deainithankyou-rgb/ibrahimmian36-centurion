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
  rcases q3 with ⟨d3, a3⟩
  rcases q5 with ⟨d5, a5⟩
  rcases q7 with ⟨d7, a7⟩
  rcases q13 with ⟨d13, a13⟩
  simp only at hq3mod hq5mod hq7mod hq13mod
  subst d3
  subst d5
  subst d7
  subst d13
  let U : Finset (ℕ × ℕ) := {(3,a3), (5,a5), (7,a7), (13,a13)}
  have hlow : 5184 ≤ (multiCore 12285 U).card := by
    have h := uncovered_card_ge (N := 12285) U
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
  exact no_cover_of_four_forced_primes S (3,a3) (5,a5) (7,a7) (13,a13)
    (by norm_num) hdvd hone hres hinj hcov
    hq3S hq5S hq7S hq13S
    rfl rfl rfl rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [U]) residual_capacity_12285
