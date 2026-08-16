import Erdos7.Capacity
import Erdos7.Bridge10395
import Erdos7.Bridge12285
import Erdos7.Bridge17325

/-!
Step-4 exclusions for the 20 new odd abundant-or-perfect candidates in
`10000 < N ≤ 20000`. Seventeen are discharged by the upstream capacity rule;
the three former stragglers use the new structural certificates.
-/

set_option maxRecDepth 800000

section
variable {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
variable (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
variable (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i))

theorem no_covering_lcm_dvd_11025 : ¬ Finset.univ.lcm n ∣ 11025 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_11655 : ¬ Finset.univ.lcm n ∣ 11655 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7,37} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_12705 : ¬ Finset.univ.lcm n ∣ 12705 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7,11} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_12915 : ¬ Finset.univ.lcm n ∣ 12915 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7,41} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_13545 : ¬ Finset.univ.lcm n ∣ 13545 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7,43} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_14175 : ¬ Finset.univ.lcm n ∣ 14175 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_14805 : ¬ Finset.univ.lcm n ∣ 14805 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7,47} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_15015 : ¬ Finset.univ.lcm n ∣ 15015 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7,11,13} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_15435 : ¬ Finset.univ.lcm n ∣ 15435 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_16065 : ¬ Finset.univ.lcm n ∣ 16065 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7,17} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_16695 : ¬ Finset.univ.lcm n ∣ 16695 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7,53} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_17955 : ¬ Finset.univ.lcm n ∣ 17955 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7,19} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_18585 : ¬ Finset.univ.lcm n ∣ 18585 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7,59} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_19215 : ¬ Finset.univ.lcm n ∣ 19215 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7,61} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_19305 : ¬ Finset.univ.lcm n ∣ 19305 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,11,13} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_19635 : ¬ Finset.univ.lcm n ∣ 19635 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7,11,17} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

theorem no_covering_lcm_dvd_19845 : ¬ Finset.univ.lcm n ∣ 19845 := fun hdvd =>
  capacity_exclusion_int n a hgt hinj hcov (by norm_num) hdvd
    ({3,5,7} : Finset ℕ) (by decide) (by decide) (by decide) (by decide)

end

def newOddAbundant10000To20000 : Finset ℕ :=
  {10395,11025,11655,12285,12705,12915,13545,14175,14805,15015,
   15435,16065,16695,17325,17955,18585,19215,19305,19635,19845}

theorem covering_lcm_notMem_newOddAbundant10000To20000
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    Finset.univ.lcm n ∉ newOddAbundant10000To20000 := by
  intro hmem
  simp only [newOddAbundant10000To20000, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact no_covering_lcm_dvd_10395_structural n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_11025 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_11655 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_12285_structural n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_12705 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_12915 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_13545 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_14175 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_14805 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_15015 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_15435 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_16065 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_16695 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_17325_structural n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_17955 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_18585 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_19215 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_19305 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_19635 n a hgt hinj hcov (dvd_of_eq h)
  · exact no_covering_lcm_dvd_19845 n a hgt hinj hcov (dvd_of_eq h)
