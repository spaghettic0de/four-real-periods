import CertifiedDiscovery.PinwheelBalanced
import CertifiedDiscovery.PinwheelTables
namespace CertifiedDiscovery.Pinwheel

noncomputable def group1 (u : ℝ) (i : Fin 4) (t : ℤ) : ℤ :=
  match i.val with
  | 0 => splitCount (balancedF u) 1 0 t
  | 1 => splitCount (balancedG u) 3 0 t
  | 2 => splitCount (balancedG u) 3 1 t
  | _ => splitCount (balancedG u) 3 2 t

theorem group1_valid (r0 r1 r2 r3 u : ℝ)
    (hr : ∀ i, 0 ≤ rates r0 r1 r2 r3 i)
    (h0 : 1*r0 ≤ u)
    (h1 : 3*r1 ≤ 1-u)
    (h2 : 3*r2 ≤ 1-u)
    (h3 : 3*r3 ≤ 1-u)
    : CumulativeValid (rates r0 r1 r2 r3) (group1 u) := by
  apply cumulative_of_bound _ _ hr
  · intro t
    have hG := split_sum_three (balancedG u t)
    norm_num [group1, splitCount]
    dsimp [balancedG] at *
    omega
  · intro i
    fin_cases i
    · simpa [CountBound, group1, rates] using split_bound (balancedF u) u r0 1 0 (by decide) (balancedF_bound u) (by norm_num; linarith)
    · simpa [CountBound, group1, rates] using split_bound (balancedG u) (1-u) r1 3 0 (by decide) (balancedG_bound u) (by norm_num; linarith)
    · simpa [CountBound, group1, rates] using split_bound (balancedG u) (1-u) r2 3 1 (by decide) (balancedG_bound u) (by norm_num; linarith)
    · simpa [CountBound, group1, rates] using split_bound (balancedG u) (1-u) r3 3 2 (by decide) (balancedG_bound u) (by norm_num; linarith)

noncomputable def group2 (u : ℝ) (i : Fin 4) (t : ℤ) : ℤ :=
  match i.val with
  | 0 => splitCount (balancedF u) 2 0 t
  | 1 => splitCount (balancedF u) 2 1 t
  | 2 => splitCount (balancedG u) 2 0 t
  | _ => splitCount (balancedG u) 2 1 t

theorem group2_valid (r0 r1 r2 r3 u : ℝ)
    (hr : ∀ i, 0 ≤ rates r0 r1 r2 r3 i)
    (h0 : 2*r0 ≤ u)
    (h1 : 2*r1 ≤ u)
    (h2 : 2*r2 ≤ 1-u)
    (h3 : 2*r3 ≤ 1-u)
    : CumulativeValid (rates r0 r1 r2 r3) (group2 u) := by
  apply cumulative_of_bound _ _ hr
  · intro t
    have hF := split_sum_two (balancedF u t)
    have hG := split_sum_two (balancedG u t)
    norm_num [group2, splitCount]
    dsimp [balancedG] at *
    omega
  · intro i
    fin_cases i
    · simpa [CountBound, group2, rates] using split_bound (balancedF u) u r0 2 0 (by decide) (balancedF_bound u) (by norm_num; linarith)
    · simpa [CountBound, group2, rates] using split_bound (balancedF u) u r1 2 1 (by decide) (balancedF_bound u) (by norm_num; linarith)
    · simpa [CountBound, group2, rates] using split_bound (balancedG u) (1-u) r2 2 0 (by decide) (balancedG_bound u) (by norm_num; linarith)
    · simpa [CountBound, group2, rates] using split_bound (balancedG u) (1-u) r3 2 1 (by decide) (balancedG_bound u) (by norm_num; linarith)

noncomputable def group3 (u : ℝ) (i : Fin 4) (t : ℤ) : ℤ :=
  match i.val with
  | 0 => splitCount (balancedF u) 3 0 t
  | 1 => splitCount (balancedF u) 3 1 t
  | 2 => splitCount (balancedF u) 3 2 t
  | _ => splitCount (balancedG u) 1 0 t

theorem group3_valid (r0 r1 r2 r3 u : ℝ)
    (hr : ∀ i, 0 ≤ rates r0 r1 r2 r3 i)
    (h0 : 3*r0 ≤ u)
    (h1 : 3*r1 ≤ u)
    (h2 : 3*r2 ≤ u)
    (h3 : 1*r3 ≤ 1-u)
    : CumulativeValid (rates r0 r1 r2 r3) (group3 u) := by
  apply cumulative_of_bound _ _ hr
  · intro t
    have hF := split_sum_three (balancedF u t)
    norm_num [group3, splitCount]
    dsimp [balancedG] at *
    omega
  · intro i
    fin_cases i
    · simpa [CountBound, group3, rates] using split_bound (balancedF u) u r0 3 0 (by decide) (balancedF_bound u) (by norm_num; linarith)
    · simpa [CountBound, group3, rates] using split_bound (balancedF u) u r1 3 1 (by decide) (balancedF_bound u) (by norm_num; linarith)
    · simpa [CountBound, group3, rates] using split_bound (balancedF u) u r2 3 2 (by decide) (balancedF_bound u) (by norm_num; linarith)
    · simpa [CountBound, group3, rates] using split_bound (balancedG u) (1-u) r3 1 0 (by decide) (balancedG_bound u) (by norm_num; linarith)

end CertifiedDiscovery.Pinwheel
