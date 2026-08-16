import Erdos7.Capacity
import Erdos7.Certificate10395
import Erdos7.MultiCoreCapacity

/-! End-to-end structural exclusion of the first upstream straggler 10395. -/

def fourPrimeCap10395 (d : ℕ) : ℕ :=
  min (onePrimeCap 10395 3 d)
    (min (onePrimeCap 10395 5 d)
      (min (onePrimeCap 10395 7 d) (onePrimeCap 10395 11 d)))

def remainingDivisors10395 : Finset ℕ :=
  (((((10395 : ℕ).divisors.erase 1).erase 3).erase 5).erase 7).erase 11

set_option maxRecDepth 100000 in
private theorem residual_capacity_10395 :
    ∑ d ∈ remainingDivisors10395, fourPrimeCap10395 d < 4320 := by
  decide

/-- There is no finite covering of `[0,10395)` by distinct moduli > 1, all
of which divide 10395. -/
theorem no_distinct_divisor_cover_10395
    (S : Finset (ℕ × ℕ))
    (hdvd : ∀ q ∈ S, q.1 ∣ 10395)
    (hone : ∀ q ∈ S, 1 < q.1)
    (hres : ∀ q ∈ S, q.2 < q.1)
    (hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)))
    (hcov : ∀ x < 10395, ∃ q ∈ S, x % q.1 = q.2) : False := by
  classical
  obtain ⟨h3, h5, h7, h11⟩ := forced_primes_10395 S hdvd hone hres hinj hcov
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
  have hUS : U ⊆ S := by
    intro q hq
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq | hq | hq
    · simpa [hq] using hq3S
    · simpa [hq] using hq5S
    · simpa [hq] using hq7S
    · simpa [hq] using hq11S
  have ha3 : a3 < 3 := by simpa using hres (3,a3) hq3S
  have ha5 : a5 < 5 := by simpa using hres (5,a5) hq5S
  have ha7 : a7 < 7 := by simpa using hres (7,a7) hq7S
  have ha11 : a11 < 11 := by simpa using hres (11,a11) hq11S
  have hlow : 4320 ≤ (multiCore 10395 U).card := by
    have h := uncovered_card_ge (N := 10395) U
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
          norm_num at hpq ⊢)
    simpa [multiCore, U] using h
  let R : Finset (ℕ × ℕ) := S \ U
  have hcoverCore : multiCore 10395 U ⊆ R.biUnion (multiCoreClass 10395 U) := by
    simpa [R] using multiCore_covered_by_residual S U hUS hcov
  have hclassCap : ∀ q ∈ R,
      (multiCoreClass 10395 U q).card ≤ fourPrimeCap10395 q.1 := by
    intro q hqR
    have hqS : q ∈ S := (Finset.mem_sdiff.mp hqR).1
    have hqd := hdvd q hqS
    have h3cap := multiCoreClass_card_le_onePrime U (3,a3) q
      (by simp [U]) (by norm_num) (by norm_num) ha3 hqd
    have h5cap := multiCoreClass_card_le_onePrime U (5,a5) q
      (by simp [U]) (by norm_num) (by norm_num) ha5 hqd
    have h7cap := multiCoreClass_card_le_onePrime U (7,a7) q
      (by simp [U]) (by norm_num) (by norm_num) ha7 hqd
    have h11cap := multiCoreClass_card_le_onePrime U (11,a11) q
      (by simp [U]) (by norm_num) (by norm_num) ha11 hqd
    exact le_min h3cap (le_min h5cap (le_min h7cap h11cap))
  have hupperR : (multiCore 10395 U).card ≤
      ∑ q ∈ R, fourPrimeCap10395 q.1 := by
    calc
      (multiCore 10395 U).card
          ≤ (R.biUnion (multiCoreClass 10395 U)).card := Finset.card_le_card hcoverCore
      _ ≤ ∑ q ∈ R, (multiCoreClass 10395 U q).card := Finset.card_biUnion_le
      _ ≤ ∑ q ∈ R, fourPrimeCap10395 q.1 :=
        Finset.sum_le_sum (fun q hq => hclassCap q hq)
  have hinjR : Set.InjOn Prod.fst (R : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact hinj (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1 hab
  have hsumImage :
      ∑ d ∈ R.image Prod.fst, fourPrimeCap10395 d =
        ∑ q ∈ R, fourPrimeCap10395 q.1 := Finset.sum_image hinjR
  have hsub : R.image Prod.fst ⊆ remainingDivisors10395 := by
    intro d hd
    obtain ⟨q, hqR, rfl⟩ := Finset.mem_image.mp hd
    have hqS : q ∈ S := (Finset.mem_sdiff.mp hqR).1
    have hqnotU : q ∉ U := (Finset.mem_sdiff.mp hqR).2
    have hn3 : q.1 ≠ 3 := by
      intro he
      have heq : q = (3,a3) := hinj hqS hq3S (by simpa using he)
      exact hqnotU (by simpa [U, heq])
    have hn5 : q.1 ≠ 5 := by
      intro he
      have heq : q = (5,a5) := hinj hqS hq5S (by simpa using he)
      exact hqnotU (by simpa [U, heq])
    have hn7 : q.1 ≠ 7 := by
      intro he
      have heq : q = (7,a7) := hinj hqS hq7S (by simpa using he)
      exact hqnotU (by simpa [U, heq])
    have hn11 : q.1 ≠ 11 := by
      intro he
      have heq : q = (11,a11) := hinj hqS hq11S (by simpa using he)
      exact hqnotU (by simpa [U, heq])
    rw [remainingDivisors10395]
    repeat' apply Finset.mem_erase.mpr
    exact ⟨hn11, hn7, hn5, hn3, (hone q hqS).ne',
      (Nat.mem_divisors.mpr ⟨hdvd q hqS, by norm_num⟩)⟩
  have hsumMono : ∑ d ∈ R.image Prod.fst, fourPrimeCap10395 d ≤
      ∑ d ∈ remainingDivisors10395, fourPrimeCap10395 d :=
    Finset.sum_le_sum_of_subset hsub
  rw [hsumImage] at hsumMono
  have hupper : (multiCore 10395 U).card < 4320 :=
    lt_of_le_of_le hupperR (lt_of_le_of_lt hsumMono residual_capacity_10395)
  omega
