import Erdos7.IntegerBridgeGeneric
import Erdos7.NoCover17325

open Finset in
theorem no_covering_lcm_dvd_17325_structural
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 17325 := by
  exact integer_cover_excluded_by_finite no_distinct_divisor_cover_17325
    n a hgt hinj hcov
