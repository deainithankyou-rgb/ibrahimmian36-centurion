import Mathlib

/-! Standalone cardinality bounds for a single congruence class. -/

def rawClass (N : ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun x => x % q.1 = q.2)

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

/-- A covering of `[0,N)` by distinct indexed classes satisfies the elementary
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
