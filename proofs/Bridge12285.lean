import Erdos7.IntegerBridgeGeneric
import Erdos7.NoCover12285

open Finset in
theorem no_covering_lcm_dvd_12285_structural
    {ι : Type} [Fintype ι] (n : ι → ℕ) (a : ι → ℤ)
    (hgt : ∀ i, 1 < n i) (hinj : Function.Injective n)
    (hcov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ (x - a i)) :
    ¬ Finset.univ.lcm n ∣ 12285 := by
  exact integer_cover_excluded_by_finite no_distinct_divisor_cover_12285
    n a hgt hinj hcov
