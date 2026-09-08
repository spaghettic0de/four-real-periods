import CertifiedDiscovery.PinwheelTable
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace CertifiedDiscovery.Pinwheel

def CountBound (u : ℝ) (F : ℤ → ℤ) : Prop :=
  ∀ (m L : ℤ), 0 ≤ L → (L : ℝ) * u < ((F (m+L) - F m : ℤ) : ℝ) + 1

noncomputable def balancedF (u : ℝ) (t : ℤ) : ℤ := ⌊(t : ℝ) * u⌋
noncomputable def balancedG (u : ℝ) (t : ℤ) : ℤ := t - balancedF u t

theorem balancedF_bound (u : ℝ) : CountBound u (balancedF u) := by
  intro m L _
  dsimp [balancedF]
  push_cast
  have h0 := Int.floor_le ((m : ℝ)*u)
  have h1 := Int.lt_floor_add_one (((m : ℝ)+(L : ℝ))*u)
  nlinarith only [h0, h1]

theorem balancedG_bound (u : ℝ) : CountBound (1-u) (balancedG u) := by
  intro m L _
  dsimp [balancedG, balancedF]
  push_cast
  have h0 := Int.lt_floor_add_one ((m : ℝ)*u)
  have h1 := Int.floor_le (((m : ℝ)+(L : ℝ))*u)
  nlinarith only [h0, h1]

def splitCount (F : ℤ → ℤ) (k off : ℤ) (t : ℤ) : ℤ := (F t + off) / k

theorem split_bound (F : ℤ → ℤ) (u r : ℝ) (k off : ℤ)
    (hk : 0 < k) (h : CountBound u F) (hr : (k : ℝ)*r ≤ u) :
    CountBound r (splitCount F k off) := by
  intro m L hL
  let A := F m + off
  let B := F (m+L) + off
  have hA0 := Int.emod_nonneg A (ne_of_gt hk)
  have hBk := Int.emod_lt_of_pos B hk
  have hAd := Int.emod_add_ediv_mul A k
  have hBd := Int.emod_add_ediv_mul B k
  have hInt : B - A + 1 ≤ k * (B/k - A/k + 1) := by nlinarith
  have hR : ((B - A : ℤ) : ℝ) + 1 ≤ (k : ℝ) * (((B/k - A/k : ℤ) : ℝ) + 1) := by
    exact_mod_cast hInt
  have hb := h m L hL
  have hdiff : B - A = F (m+L) - F m := by dsimp [A, B]; omega
  rw [hdiff] at hR
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hLR : (0 : ℝ) ≤ L := by exact_mod_cast hL
  apply (mul_lt_mul_iff_right₀ hkR).mp
  change (k : ℝ) * ((L : ℝ) * r) < (k : ℝ) * (((B/k - A/k : ℤ) : ℝ) + 1)
  calc
    (k : ℝ) * ((L : ℝ) * r) = (L : ℝ) * ((k : ℝ)*r) := by ring1
    _ ≤ (L : ℝ)*u := mul_le_mul_of_nonneg_left hr hLR
    _ < ((F (m+L) - F m : ℤ) : ℝ) + 1 := hb
    _ ≤ _ := hR

theorem split_sum_two (z : ℤ) : z/2 + (z+1)/2 = z := by omega
theorem split_sum_three (z : ℤ) : z/3 + (z+1)/3 + (z+2)/3 = z := by omega

theorem cumulative_of_bound (r : Fin 4 → ℝ) (F : Fin 4 → ℤ → ℤ)
    (hr : ∀ i, 0 ≤ r i)
    (hsum : ∀ t, F 0 t + F 1 t + F 2 t + F 3 t = t)
    (hb : ∀ i, CountBound (r i) (F i)) : CumulativeValid r F := by
  refine ⟨?_, ?_, hb⟩
  · intro i t
    have hg := hb i t 1 (by decide)
    have hp := hr i
    by_contra h
    have hz : F i (t+1) - F i t ≤ -1 := by omega
    have hzR : ((F i (t+1) - F i t : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hz
    norm_num at hg hzR
    linarith
  · intro t
    have h0 := hsum t
    have h1 := hsum (t+1)
    omega

end CertifiedDiscovery.Pinwheel
