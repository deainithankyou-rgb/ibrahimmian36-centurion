import Mathlib

/-! Standalone cardinality bounds for a single congruence class. -/

def rawClass (N : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun x => x % q.1 = q.2)

def avoidClass (N p a : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun x => x % p ≠ a)

/-- If `d ∣ N`, a single residue class modulo `d` occupies at most `N / d`
points of `[0,N)`. -/
theorem card_class_mod_le (N d r : ℕ) (hd : d ∣ N) :
    ((Finset.range N).filter (fun x => x % d = r)).card ≤ N / d := by
  classical
  let T := Finset.range (N / d)
  have hmap : ∀ x ∈ (Finset.range N).filter (fun x => x % d = r), x / d ∈ T := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    exact Finset.mem_range.mpr (Nat.div_lt_div_of_lt_of_dvd hd hx.1)
  have hinj : Set.InjOn (fun x : ℕ => x / d)
      (((Finset.range N).filter (fun x => x % d = r) : Finset ℕ) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
    have hmod : x ≡ y [MOD d] := by
      change x % d = y % d
      rw [hx.2, hy.2]
    exact Nat.ext_div_modEq hxy hmod
  have hcard :
      ((Finset.range N).filter (fun x => x % d = r)).card ≤ T.card := by
    exact Finset.card_le_card_of_injOn (fun x => x / d) hmap hinj
  simpa [T] using hcard

/-- Avoiding one normalized residue modulo a divisor `p` leaves at least the
standard `(N/p)(p-1)` points. -/
theorem avoid_class_card_ge (N p a : ℕ) (hd : p ∣ N) (ha : a < p) :
    (N / p) * (p - 1) ≤ (avoidClass N p a).card := by
  classical
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le a) ha
  let T := Finset.range (N / p) ×ˢ ((Finset.range p).erase a)
  have hmap : ∀ bk ∈ T, p * bk.1 + bk.2 ∈ avoidClass N p a := by
    rintro ⟨k, r⟩ hkr
    rw [Finset.mem_product] at hkr
    rcases hkr with ⟨hk, hr⟩
    have hklt : k < N / p := Finset.mem_range.mp hk
    have hrlt : r < p := Finset.mem_range.mp (Finset.mem_of_mem_erase hr)
    have hlt : p * k + r < N := by
      calc
        p * k + r < p * k + p := Nat.add_lt_add_left hrlt _
        _ = p * (k + 1) := by simp [Nat.mul_add]
        _ ≤ p * (N / p) := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hklt)
        _ = N := Nat.mul_div_cancel' hd
    rw [avoidClass, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact hlt
    · have hrne : r ≠ a := Finset.ne_of_mem_erase hr
      simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mod_eq_of_lt hrlt] using hrne
  have hinj : Set.InjOn (fun bk : ℕ × ℕ => p * bk.1 + bk.2) (T : Set (ℕ × ℕ)) := by
    rintro ⟨k, r⟩ hkr ⟨k', r'⟩ hkr' heq
    rw [Finset.mem_coe, Finset.mem_product] at hkr hkr'
    have hrlt : r < p := Finset.mem_range.mp (Finset.mem_of_mem_erase hkr.2)
    have hrlt' : r' < p := Finset.mem_range.mp (Finset.mem_of_mem_erase hkr'.2)
    have hmodEq := congrArg (fun x : ℕ => x % p) heq
    have hmod : r = r' := by
      simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_self,
        Nat.mod_eq_of_lt hrlt, Nat.mod_eq_of_lt hrlt'] using hmodEq
    subst r'
    have hpk : p * k = p * k' := Nat.add_right_cancel heq
    have hkEq : k = k' := Nat.eq_of_mul_eq_mul_left hp hpk
    subst k'
    rfl
  have hcard : T.card ≤ (avoidClass N p a).card :=
    Finset.card_le_card_of_injOn (fun bk : ℕ × ℕ => p * bk.1 + bk.2) hmap hinj
  have hamem : a ∈ Finset.range p := Finset.mem_range.mpr ha
  have hT : T.card = (N / p) * (p - 1) := by
    simp [T, Finset.card_product, Finset.card_erase_of_mem hamem]
  rw [hT] at hcard
  exact hcard

/-- A covering of `[0,N)` by indexed classes satisfies the elementary
sum-capacity inequality. -/
theorem covering_raw_capacity
    (N : ℕ) (S : Finset (ℕ × ℕ))
    (hdvd : ∀ q ∈ S, q.1 ∣ N)
    (hcov : ∀ x < N, ∃ q ∈ S, x % q.1 = q.2) :
    N ≤ ∑ q ∈ S, N / q.1 := by
  classical
  have hcover : Finset.range N ⊆ S.biUnion (rawClass N) := by
    intro x hx
    have hxN : x < N := Finset.mem_range.mp hx
    obtain ⟨q, hqS, hqx⟩ := hcov x hxN
    exact Finset.mem_biUnion.mpr ⟨q, hqS, by
      simp [rawClass, hxN, hqx]⟩
  calc
    N = (Finset.range N).card := by simp
    _ ≤ (S.biUnion (rawClass N)).card := Finset.card_le_card hcover
    _ ≤ ∑ q ∈ S, (rawClass N q).card := Finset.card_biUnion_le
    _ ≤ ∑ q ∈ S, N / q.1 := by
      exact Finset.sum_le_sum (fun q hq => by
        simpa [rawClass] using card_class_mod_le N q.1 q.2 (hdvd q hq))
