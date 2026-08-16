import Erdos7.MultiCoreCapacity

/-!
Reusable final-stage certificate for four already-forced prime classes.
The search/compiler supplies the four forced classes, a lower bound for the
residual core, and one closed arithmetic inequality.  Lean checks the rest.
-/

def fourPrimeCap (N p1 p2 p3 p4 d : ℕ) : ℕ :=
  min (onePrimeCap N p1 d)
    (min (onePrimeCap N p2 d)
      (min (onePrimeCap N p3 d) (onePrimeCap N p4 d)))

def remainingAfterFour (N p1 p2 p3 p4 : ℕ) : Finset ℕ :=
  (((((N.divisors.erase 1).erase p1).erase p2).erase p3).erase p4)

/-- If four specified prime classes are already forced, and the residual
multi-core is larger than the sum of the best one-prime capacities of every
remaining divisor modulus, then no covering exists. -/
theorem no_cover_of_four_forced_primes
    {N L p1 p2 p3 p4 : ℕ}
    (S : Finset (ℕ × ℕ))
    (q1 q2 q3 q4 : ℕ × ℕ)
    (hdvd : ∀ q ∈ S, q.1 ∣ N)
    (hone : ∀ q ∈ S, 1 < q.1)
    (hres : ∀ q ∈ S, q.2 < q.1)
    (hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)))
    (hcov : ∀ x < N, ∃ q ∈ S, x % q.1 = q.2)
    (hq1S : q1 ∈ S) (hq2S : q2 ∈ S) (hq3S : q3 ∈ S) (hq4S : q4 ∈ S)
    (hq1mod : q1.1 = p1) (hq2mod : q2.1 = p2)
    (hq3mod : q3.1 = p3) (hq4mod : q4.1 = p4)
    (hp1prime : p1.Prime) (hp2prime : p2.Prime)
    (hp3prime : p3.Prime) (hp4prime : p4.Prime)
    (hp1dvd : p1 ∣ N) (hp2dvd : p2 ∣ N) (hp3dvd : p3 ∣ N) (hp4dvd : p4 ∣ N)
    (hlow : L ≤ (multiCore N {q1,q2,q3,q4}).card)
    (harith : ∑ d ∈ remainingAfterFour N p1 p2 p3 p4,
        fourPrimeCap N p1 p2 p3 p4 d < L) : False := by
  classical
  let U : Finset (ℕ × ℕ) := {q1,q2,q3,q4}
  let R : Finset (ℕ × ℕ) := S \ U
  have hcoverCore : multiCore N U ⊆ R.biUnion (multiCoreClass N U) := by
    have hUS : U ⊆ S := by
      intro q hq
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact hq1S
      · exact hq2S
      · exact hq3S
      · exact hq4S
    simpa [R] using multiCore_covered_by_residual S U hUS hcov
  have hq1res : q1.2 < p1 := by simpa [hq1mod] using hres q1 hq1S
  have hq2res : q2.2 < p2 := by simpa [hq2mod] using hres q2 hq2S
  have hq3res : q3.2 < p3 := by simpa [hq3mod] using hres q3 hq3S
  have hq4res : q4.2 < p4 := by simpa [hq4mod] using hres q4 hq4S
  have hclassCap : ∀ q ∈ R,
      (multiCoreClass N U q).card ≤ fourPrimeCap N p1 p2 p3 p4 q.1 := by
    intro q hqR
    have hqS : q ∈ S := (Finset.mem_sdiff.mp hqR).1
    have hqd := hdvd q hqS
    have h1 := multiCoreClass_card_le_onePrime U q1 q
      (by simp [U]) (by simpa [hq1mod] using hp1prime)
      (by simpa [hq1mod] using hp1dvd)
      (by simpa [hq1mod] using hq1res) hqd
    have h2 := multiCoreClass_card_le_onePrime U q2 q
      (by simp [U]) (by simpa [hq2mod] using hp2prime)
      (by simpa [hq2mod] using hp2dvd)
      (by simpa [hq2mod] using hq2res) hqd
    have h3 := multiCoreClass_card_le_onePrime U q3 q
      (by simp [U]) (by simpa [hq3mod] using hp3prime)
      (by simpa [hq3mod] using hp3dvd)
      (by simpa [hq3mod] using hq3res) hqd
    have h4 := multiCoreClass_card_le_onePrime U q4 q
      (by simp [U]) (by simpa [hq4mod] using hp4prime)
      (by simpa [hq4mod] using hp4dvd)
      (by simpa [hq4mod] using hq4res) hqd
    exact le_min h1 (le_min h2 (le_min h3 h4))
  have hupperR : (multiCore N U).card ≤
      ∑ q ∈ R, fourPrimeCap N p1 p2 p3 p4 q.1 := by
    calc
      (multiCore N U).card ≤ (R.biUnion (multiCoreClass N U)).card :=
        Finset.card_le_card hcoverCore
      _ ≤ ∑ q ∈ R, (multiCoreClass N U q).card := Finset.card_biUnion_le
      _ ≤ ∑ q ∈ R, fourPrimeCap N p1 p2 p3 p4 q.1 :=
        Finset.sum_le_sum (fun q hq => hclassCap q hq)
  have hinjR : Set.InjOn Prod.fst (R : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact hinj (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1 hab
  have hsumImage :
      ∑ d ∈ R.image Prod.fst, fourPrimeCap N p1 p2 p3 p4 d =
        ∑ q ∈ R, fourPrimeCap N p1 p2 p3 p4 q.1 := Finset.sum_image hinjR
  have hsub : R.image Prod.fst ⊆ remainingAfterFour N p1 p2 p3 p4 := by
    intro d hd
    obtain ⟨q, hqR, rfl⟩ := Finset.mem_image.mp hd
    have hqS : q ∈ S := (Finset.mem_sdiff.mp hqR).1
    have hqnotU : q ∉ U := (Finset.mem_sdiff.mp hqR).2
    have hn1 : q.1 ≠ p1 := by
      intro he
      have heq : q = q1 := hinj hqS hq1S (he.trans hq1mod.symm)
      exact hqnotU (by simp [U, heq])
    have hn2 : q.1 ≠ p2 := by
      intro he
      have heq : q = q2 := hinj hqS hq2S (he.trans hq2mod.symm)
      exact hqnotU (by simp [U, heq])
    have hn3 : q.1 ≠ p3 := by
      intro he
      have heq : q = q3 := hinj hqS hq3S (he.trans hq3mod.symm)
      exact hqnotU (by simp [U, heq])
    have hn4 : q.1 ≠ p4 := by
      intro he
      have heq : q = q4 := hinj hqS hq4S (he.trans hq4mod.symm)
      exact hqnotU (by simp [U, heq])
    rw [remainingAfterFour]
    exact Finset.mem_erase.mpr ⟨hn4,
      Finset.mem_erase.mpr ⟨hn3,
        Finset.mem_erase.mpr ⟨hn2,
          Finset.mem_erase.mpr ⟨hn1,
            Finset.mem_erase.mpr ⟨(hone q hqS).ne',
              Nat.mem_divisors.mpr ⟨hdvd q hqS,
                Nat.pos_of_dvd_of_pos (hdvd q hqS) (by omega) |>.ne'⟩⟩⟩⟩⟩⟩
  have hsumMono :
      ∑ d ∈ R.image Prod.fst, fourPrimeCap N p1 p2 p3 p4 d ≤
        ∑ d ∈ remainingAfterFour N p1 p2 p3 p4, fourPrimeCap N p1 p2 p3 p4 d :=
    Finset.sum_le_sum_of_subset hsub
  rw [hsumImage] at hsumMono
  have hcapR : ∑ q ∈ R, fourPrimeCap N p1 p2 p3 p4 q.1 < L :=
    lt_of_le_of_lt hsumMono harith
  have hupper : (multiCore N U).card < L := lt_of_le_of_lt hupperR hcapR
  have hlow' : L ≤ (multiCore N U).card := by simpa [U] using hlow
  omega
