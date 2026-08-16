import Erdos7.Enumeration
import Erdos7.Capacity20000

/-!
Kernel enumeration and composed headline extending the upstream `>10000`
bound to `>20000`.
-/

def sigma141 (n : ℕ) : ℕ := sigmaPairAux n 141 0

theorem sigma141_eq_sigma (n : ℕ) (hn : 0 < n)
    (hbound : n < (141 + 1) * (141 + 1)) :
    sigma141 n = ∑ d ∈ n.divisors, d := by
  exact sigmaPair_eq_sigma n 141 hn hbound

def newOddAbundantList10000To20000 : List ℕ :=
  [10395,11025,11655,12285,12705,12915,13545,14175,14805,15015,
   15435,16065,16695,17325,17955,18585,19215,19305,19635,19845]

def enumOk20000 : ℕ → Bool
  | 0 => true
  | L + 1 =>
    (decide (L + 1 ≤ 10000)
      || (decide ((L + 1) % 2 = 0)
        || (decide ((L + 1) ∈ newOddAbundantList10000To20000)
          || decide (sigma141 (L + 1) < 2 * (L + 1)))))
    && enumOk20000 L

theorem mem_newOddAbundant_of_mem_list {l : ℕ}
    (h : l ∈ newOddAbundantList10000To20000) :
    l ∈ newOddAbundant10000To20000 := by
  fin_cases h <;> decide

theorem enumOk20000_sound : ∀ X, enumOk20000 X = true →
    ∀ l, l ≤ X → 10000 < l → l % 2 = 1 →
      2 * l ≤ sigma141 l → l ∈ newOddAbundant10000To20000 := by
  intro X
  induction X with
  | zero =>
      intro _ l hl hlo _ _
      omega
  | succ X ih =>
      intro h l hl hlo hodd hab
      rw [enumOk20000, Bool.and_eq_true] at h
      obtain ⟨hhead, htail⟩ := h
      rcases Nat.lt_or_ge l (X + 1) with hlt | hge
      · exact ih htail l (by omega) hlo hodd hab
      · have hleq : l = X + 1 := by omega
        subst hleq
        rw [Bool.or_eq_true] at hhead
        rcases hhead with hsmall | hrest
        · rw [decide_eq_true_iff] at hsmall
          omega
        · rw [Bool.or_eq_true] at hrest
          rcases hrest with heven | hrest
          · rw [decide_eq_true_iff] at heven
            omega
          · rw [Bool.or_eq_true] at hrest
            rcases hrest with hlist | hsig
            · rw [decide_eq_true_iff] at hlist
              exact mem_newOddAbundant_of_mem_list hlist
            · rw [decide_eq_true_iff] at hsig
              omega

set_option maxRecDepth 6000000 in
set_option maxHeartbeats 80000000 in
theorem enum_ok_20000 : enumOk20000 20000 = true := by
  decide

theorem new_odd_abundant_10000_20000_mem
    (L : ℕ) (hlo : 10000 < L) (hle : L ≤ 20000)
    (hodd : L % 2 = 1)
    (hab : 2 * L ≤ ∑ d ∈ L.divisors, d) :
    L ∈ newOddAbundant10000To20000 := by
  have hab' : 2 * L ≤ sigma141 L := by
    rw [sigma141_eq_sigma L (by omega) (by norm_num; omega)]
    exact hab
  exact enumOk20000_sound 20000 enum_ok_20000 L hle hlo hodd hab'

open Finset in
/-- **Extended headline.** Any covering of `ℤ` by finitely many congruence
classes with distinct odd moduli `>1` has lcm strictly greater than 20000. -/
theorem odd_covering_lcm_gt_20000
    {ι : Type} [Fintype ι]
    (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hodd : ∀ i, Odd (n i))
    (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    20000 < Finset.univ.lcm n := by
  classical
  have hgt10000 := odd_covering_lcm_gt_10000 n a hgt hodd hinj hcov
  by_contra hle
  rw [not_lt] at hle
  set L := Finset.univ.lcm n with hLdef
  have hLgt : 10000 < L := by simpa [hLdef] using hgt10000
  have hLle : L ≤ 20000 := by simpa [hLdef] using hle
  have hpos : ∀ i, 0 < n i := fun i => lt_trans Nat.zero_lt_one (hgt i)
  have hdvd : ∀ i, n i ∣ L := fun i => by
    rw [hLdef]
    exact Finset.dvd_lcm (Finset.mem_univ i)
  have hL0 : L ≠ 0 := by
    rw [hLdef, Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, -, hx⟩
    exact (hpos x).ne' hx
  have hsub : (Finset.univ.image n) ⊆ L.divisors.erase 1 := by
    intro d hd
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_erase.mpr ⟨(hgt i).ne', Nat.mem_divisors.mpr ⟨hdvd i, hL0⟩⟩
  have hdens : (1 : ℚ) ≤ ∑ i, (1 : ℚ) / n i := covering_density_ge_one n a hpos hcov
  have himg : ∑ d ∈ Finset.univ.image n, (1 : ℚ) / d = ∑ i, (1 : ℚ) / n i :=
    Finset.sum_image (fun x _ y _ h => hinj h)
  have hbridge := sum_inv_le_abundancy L hL0 (Finset.univ.image n) hsub
  rw [himg] at hbridge
  have hLq : (0 : ℚ) < (L : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hL0
  have h2 : (2 : ℚ) ≤ (∑ d ∈ L.divisors, (d : ℚ)) / L := by linarith
  have hcancel : ((∑ d ∈ L.divisors, (d : ℚ)) / (L : ℚ)) * L
      = ∑ d ∈ L.divisors, (d : ℚ) := by field_simp
  have hm := mul_le_mul_of_nonneg_right h2 hLq.le
  rw [hcancel] at hm
  have habund : 2 * L ≤ ∑ d ∈ L.divisors, d := by
    have hc : ((∑ d ∈ L.divisors, d : ℕ) : ℚ) = ∑ d ∈ L.divisors, (d : ℚ) := by
      push_cast
      ring
    rw [← hc] at hm
    exact_mod_cast hm
  have hLodd : L % 2 = 1 := by
    rcases Nat.even_or_odd L with he | ho
    · exfalso
      have hLm : L % 2 = 0 := Nat.even_iff.mp he
      have h2L : (2 : ℕ) ∣ L := by omega
      have hLp : L ∣ ∏ i, n i :=
        Finset.lcm_dvd fun i _ => Finset.dvd_prod_of_mem n (Finset.mem_univ i)
      have hprod : Odd (∏ i, n i) :=
        Finset.prod_induction _ Odd (fun x y hx hy => hx.mul hy) odd_one
          (fun i _ => hodd i)
      rw [Nat.odd_iff] at hprod
      have : (2 : ℕ) ∣ ∏ i, n i := h2L.trans hLp
      omega
    · exact Nat.odd_iff.mp ho
  have hmem := new_odd_abundant_10000_20000_mem L hLgt hLle hLodd habund
  have hnot := covering_lcm_notMem_newOddAbundant10000To20000 n a hgt hinj hcov
  exact hnot (by simpa [hLdef] using hmem)
