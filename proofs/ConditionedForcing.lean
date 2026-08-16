import Erdos7.RawCapacity
import Erdos7.OnePrimeCapacity

/-! One-prime conditioned forcing. -/

def onePrimeCap (N p d : ℕ) : ℕ :=
  if p ∣ d then N / d else (N / (d * p)) * (p - 1)

def conditionedClass (N : ℕ) (q0 q : ℕ × ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun x => x % q.1 = q.2 ∧ x % q0.1 ≠ q0.2)

def conditionedCore (N : ℕ) (q0 : ℕ × ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun x => x % q0.1 ≠ q0.2)

/-- Every residual class has the one-prime conditioned capacity. -/
theorem conditionedClass_card_le
    {N : ℕ} (q0 q : ℕ × ℕ)
    (hq0prime : q0.1.Prime) (hq0dvd : q0.1 ∣ N)
    (hq0res : q0.2 < q0.1) (hqdvd : q.1 ∣ N) :
    (conditionedClass N q0 q).card ≤ onePrimeCap N q0.1 q.1 := by
  classical
  by_cases hpq : q0.1 ∣ q.1
  · have hsub : conditionedClass N q0 q ⊆
        (Finset.range N).filter (fun x => x % q.1 = q.2) := by
      intro x hx
      simp only [conditionedClass, Finset.mem_filter, Finset.mem_range] at hx ⊢
      exact ⟨hx.1, hx.2.1⟩
    have hraw := card_class_mod_le N q.1 q.2 hqdvd
    exact (Finset.card_le_card hsub).trans (by simpa [onePrimeCap, hpq] using hraw)
  · have hcopP : q0.1.Coprime q.1 := hq0prime.coprime_iff_not_dvd.mpr hpq
    have hcop : q.1.Coprime q0.1 := hcopP.symm
    have hdp : q.1 * q0.1 ∣ N := hcop.mul_dvd_of_dvd_of_dvd hqdvd hq0dvd
    have h := card_class_avoiding_coprime_residue_le
      N q.1 q0.1 q.2 q0.2 hq0prime.pos hq0res hcop hdp
    simpa [conditionedClass, onePrimeCap, hpq] using h

/-- The core avoiding one selected prime class has the standard lower bound. -/
theorem conditionedCore_card_ge
    {N : ℕ} (q0 : ℕ × ℕ) (hq0dvd : q0.1 ∣ N) (hq0res : q0.2 < q0.1) :
    (N / q0.1) * (q0.1 - 1) ≤ (conditionedCore N q0).card := by
  simpa [conditionedCore, avoidClass] using
    avoid_class_card_ge N q0.1 q0.2 hq0dvd hq0res

/-- A covering still covers the core after deleting its selected prime class. -/
theorem conditionedCore_covered
    {N : ℕ} (S : Finset (ℕ × ℕ)) (q0 : ℕ × ℕ)
    (hq0S : q0 ∈ S)
    (hcov : ∀ x < N, ∃ q ∈ S, x % q.1 = q.2) :
    conditionedCore N q0 ⊆ (S.erase q0).biUnion (conditionedClass N q0) := by
  classical
  intro x hx
  simp only [conditionedCore, Finset.mem_filter, Finset.mem_range] at hx
  obtain ⟨q, hqS, hqx⟩ := hcov x hx.1
  have hqne : q ≠ q0 := by
    intro h
    subst q
    exact hx.2 hqx
  apply Finset.mem_biUnion.mpr
  refine ⟨q, Finset.mem_erase.mpr ⟨hqne, hqS⟩, ?_⟩
  simp only [conditionedClass, Finset.mem_filter, Finset.mem_range]
  exact ⟨hx.1, hqx, hx.2⟩

/-- If a target modulus is absent and the certified residual capacity is below
one-prime core size, contradiction; hence the target modulus is forced. -/
theorem forced_modulus_after_one_prime
    {N p d0 : ℕ} (S : Finset (ℕ × ℕ)) (Allowed : Finset ℕ)
    (q0 : ℕ × ℕ)
    (hq0S : q0 ∈ S) (hq0mod : q0.1 = p) (hq0res : q0.2 < p)
    (hpprime : p.Prime) (hpdvd : p ∣ N) (hd0p : d0 ≠ p)
    (hdvd : ∀ q ∈ S, q.1 ∣ N)
    (hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)))
    (hcov : ∀ x < N, ∃ q ∈ S, x % q.1 = q.2)
    (hallowed : ∀ q ∈ S, q.1 ∈ Allowed)
    (harith : ∑ d ∈ (Allowed.erase p).erase d0, onePrimeCap N p d <
      (N / p) * (p - 1)) :
    ∃ q ∈ S, q.1 = d0 := by
  classical
  by_contra hno
  push_neg at hno
  have hcore : (N / p) * (p - 1) ≤ (conditionedCore N q0).card := by
    rw [← hq0mod]
    exact conditionedCore_card_ge q0
      (by simpa [hq0mod] using hpdvd)
      (by simpa [hq0mod] using hq0res)
  have hcover := conditionedCore_covered S q0 hq0S hcov
  have hcap : ∀ q ∈ S.erase q0,
      (conditionedClass N q0 q).card ≤ onePrimeCap N p q.1 := by
    intro q hq
    have hqS := (Finset.mem_erase.mp hq).2
    have h := conditionedClass_card_le q0 q
      (by simpa [hq0mod] using hpprime)
      (by simpa [hq0mod] using hpdvd)
      (by simpa [hq0mod] using hq0res)
      (hdvd q hqS)
    simpa [hq0mod] using h
  have hupper : (conditionedCore N q0).card ≤
      ∑ q ∈ S.erase q0, onePrimeCap N p q.1 := by
    calc
      (conditionedCore N q0).card
          ≤ ((S.erase q0).biUnion (conditionedClass N q0)).card :=
            Finset.card_le_card hcover
      _ ≤ ∑ q ∈ S.erase q0, (conditionedClass N q0 q).card := Finset.card_biUnion_le
      _ ≤ ∑ q ∈ S.erase q0, onePrimeCap N p q.1 :=
        Finset.sum_le_sum (fun q hq => hcap q hq)
  have hinjErase : Set.InjOn Prod.fst ((S.erase q0 : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact hinj (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab
  have hsum : ∑ d ∈ (S.erase q0).image Prod.fst, onePrimeCap N p d =
      ∑ q ∈ S.erase q0, onePrimeCap N p q.1 := Finset.sum_image hinjErase
  have hsub : (S.erase q0).image Prod.fst ⊆ (Allowed.erase p).erase d0 := by
    intro d hd
    obtain ⟨q, hqErase, rfl⟩ := Finset.mem_image.mp hd
    have hqS := (Finset.mem_erase.mp hqErase).2
    have hqne0 := (Finset.mem_erase.mp hqErase).1
    have hnep : q.1 ≠ p := by
      intro heq
      have hfst : q.1 = q0.1 := heq.trans hq0mod.symm
      exact hqne0 (hinj hqS hq0S hfst)
    exact Finset.mem_erase.mpr ⟨hno q hqS,
      Finset.mem_erase.mpr ⟨hnep, hallowed q hqS⟩⟩
  have hmono : ∑ d ∈ (S.erase q0).image Prod.fst, onePrimeCap N p d ≤
      ∑ d ∈ (Allowed.erase p).erase d0, onePrimeCap N p d :=
    Finset.sum_le_sum_of_subset hsub
  rw [hsum] at hmono
  omega
