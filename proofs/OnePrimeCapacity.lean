import Mathlib

/-!
One-prime conditioned capacity.
For a modulus `d` and an avoided coprime modulus `p`, a fixed class modulo `d`
that also avoids residue `0 mod p` occupies at most
`(N / (d*p)) * (p-1)` points of `[0,N)` when `d*p ∣ N`.
-/

theorem card_class_avoiding_coprime_zero_le
    (N d p r : ℕ) (hp : 0 < p) (hcop : d.Coprime p) (hdp : d * p ∣ N) :
    ((Finset.range N).filter (fun x => x % d = r ∧ x % p ≠ 0)).card ≤
      (N / (d * p)) * (p - 1) := by
  classical
  let T := Finset.range (N / (d * p)) ×ˢ ((Finset.range p).erase 0)
  have hmap : ∀ x ∈ (Finset.range N).filter (fun x => x % d = r ∧ x % p ≠ 0),
      (x / (d * p), x % p) ∈ T := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    rw [Finset.mem_product]
    constructor
    · exact Nat.div_lt_div_of_lt_of_dvd hdp hx.1
    · rw [Finset.mem_erase]
      exact ⟨hx.2.2, Finset.mem_range.mpr (Nat.mod_lt x hp)⟩
  have hinj : Set.InjOn (fun x : ℕ => (x / (d * p), x % p))
      (((Finset.range N).filter (fun x => x % d = r ∧ x % p ≠ 0) : Finset ℕ) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
    have hq : x / (d * p) = y / (d * p) := congrArg Prod.fst hxy
    have hpmod : x ≡ y [MOD p] := by
      change x % p = y % p
      exact congrArg Prod.snd hxy
    have hdmod : x ≡ y [MOD d] := by
      change x % d = y % d
      rw [hx.2.1, hy.2.1]
    have hdpmod : x ≡ y [MOD d * p] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).2 ⟨hdmod, hpmod⟩
    exact Nat.ext_div_modEq hq hdpmod
  have hcard :
      ((Finset.range N).filter (fun x => x % d = r ∧ x % p ≠ 0)).card ≤ T.card := by
    exact Finset.card_le_card_of_injOn (fun x => (x / (d * p), x % p)) hmap hinj
  have hzero : 0 ∈ Finset.range p := Finset.mem_range.mpr hp
  rw [show T.card = (N / (d * p)) * (p - 1) by
    simp [T, Finset.card_product, Finset.card_erase_of_mem hzero]] at hcard
  exact hcard
