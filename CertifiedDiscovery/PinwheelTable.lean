import CertifiedDiscovery.PinwheelWords
import CertifiedDiscovery.PinwheelPeriodic

namespace CertifiedDiscovery.Pinwheel

/-- Integer cumulative counts specify a schedule by their unit-time increments. -/
def CumulativeValid (r : Fin 4 → ℝ) (F : Fin 4 → ℤ → ℤ) : Prop :=
  (∀ i t, F i t ≤ F i (t + 1)) ∧
  (∀ t, (F 0 (t+1) - F 0 t) + (F 1 (t+1) - F 1 t) +
    (F 2 (t+1) - F 2 t) + (F 3 (t+1) - F 3 t) = 1) ∧
  (∀ (i : Fin 4) (m L : ℤ), 0 ≤ L → (L : ℝ) * r i < ((F i (m+L) - F i m : ℤ) : ℝ) + 1)

structure PeriodicData where
  period : Nat
  counts : Fin 4 → ℤ
  pref : Fin 4 → ℤ → ℤ
  caps : Fin 4 → RateCap

def PeriodicData.eval (T : PeriodicData) (i : Fin 4) : ℤ → ℤ :=
  periodicPrefix T.period (T.counts i) (T.pref i)

def PeriodicData.Certified (T : PeriodicData) : Prop :=
  0 < T.period ∧
  (∀ i, 0 < (T.caps i).den) ∧
  (∀ (i : Fin 4) (a : Fin T.period), T.eval i a ≤ T.eval i (a+1)) ∧
  (∀ (a : Fin T.period),
    (T.eval 0 (a+1) - T.eval 0 a) + (T.eval 1 (a+1) - T.eval 1 a) +
    (T.eval 2 (a+1) - T.eval 2 a) + (T.eval 3 (a+1) - T.eval 3 a) = 1) ∧
  (∀ i, ((T.caps i).num : ℤ) * T.period ≤ (T.caps i).den * T.counts i) ∧
  (∀ (i : Fin 4) (a b : Fin T.period),
    if (T.caps i).closed then
      ((T.caps i).num : ℤ) * b < (T.caps i).den * (T.eval i (a+b) - T.eval i a + 1)
    else
      ((T.caps i).num : ℤ) * b ≤ (T.caps i).den * (T.eval i (a+b) - T.eval i a + 1))

instance (T : PeriodicData) : Decidable T.Certified := by
  unfold PeriodicData.Certified
  infer_instance

def PeriodicData.RateBounds (T : PeriodicData) (r : Fin 4 → ℝ) : Prop :=
  ∀ i, if (T.caps i).closed then ((T.caps i).den : ℝ) * r i ≤ (T.caps i).num
       else ((T.caps i).den : ℝ) * r i < (T.caps i).num

theorem PeriodicData.valid (T : PeriodicData) (h : T.Certified)
    (r : Fin 4 → ℝ) (hr : T.RateBounds r) : CumulativeValid r T.eval := by
  obtain ⟨hP, hd, hstep, hsum, hmean, hsmall⟩ := h
  have hPZ : (0 : ℤ) < T.period := by exact_mod_cast hP
  have hshift (i : Fin 4) (t q : ℤ) :
      T.eval i (t + q*T.period) = T.eval i t + q*T.counts i :=
    periodicPrefix_shift _ _ (ne_of_gt hPZ) _ _ _
  have hreduce (i : Fin 4) (t L : ℤ) :
      T.eval i (t+L) - T.eval i t =
      T.eval i (t % T.period + L) - T.eval i (t % T.period) :=
    periodic_difference_reduce _ _ _ (hshift i) _ _
  have hresidue (t : ℤ) : ∃ a : Fin T.period, (a.val : ℤ) = t % T.period := by
    have h0 := Int.emod_nonneg t (ne_of_gt hPZ)
    have hlt := Int.emod_lt_of_pos t hPZ
    exact ⟨⟨(t % T.period).toNat, by omega⟩, by simp [Int.toNat_of_nonneg h0]⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i t
    obtain ⟨a, ha⟩ := hresidue t
    have hs := hstep i a
    have he := hreduce i t 1
    rw [← ha] at he
    omega
  · intro t
    obtain ⟨a, ha⟩ := hresidue t
    have hs := hsum a
    have h0 := hreduce 0 t 1
    have h1 := hreduce 1 t 1
    have h2 := hreduce 2 t 1
    have h3 := hreduce 3 t 1
    rw [← ha] at h0 h1 h2 h3
    omega
  · intro i m L hL
    have hdR : (0 : ℝ) < (T.caps i).den := by exact_mod_cast hd i
    have hrweak : ((T.caps i).den : ℝ) * r i ≤ (T.caps i).num := by
      have hh := hr i
      cases hc : (T.caps i).closed <;> simp [hc] at hh
      · exact le_of_lt hh
      · exact hh
    have hmeanR : (T.period : ℝ) * r i ≤ T.counts i := by
      have hmR : ((T.caps i).num : ℝ) * T.period ≤
          ((T.caps i).den : ℝ) * T.counts i := by exact_mod_cast hmean i
      apply (mul_le_mul_iff_right₀ hdR).mp
      calc
        ((T.caps i).den : ℝ) * (T.period * r i) =
            (((T.caps i).den : ℝ) * r i) * T.period := by ring1
        _ ≤ ((T.caps i).num : ℝ) * T.period :=
          mul_le_mul_of_nonneg_right hrweak (by positivity)
        _ ≤ _ := hmR
    apply periodic_window_bound (T.eval i) T.period (T.counts i) (r i)
      hPZ (hshift i) hmeanR ?_ m L hL
    intro a b ha0 haP hb0 hbP
    by_cases hb : b = 0
    · subst b
      simp
    have hbpos : 0 < b := by omega
    have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
    let A : Fin T.period := ⟨a.toNat, by omega⟩
    let B : Fin T.period := ⟨b.toNat, by omega⟩
    have hA : (A.val : ℤ) = a := Int.toNat_of_nonneg ha0
    have hB : (B.val : ℤ) = b := Int.toNat_of_nonneg hb0
    have hs := hsmall i A B
    have hh := hr i
    cases hc : (T.caps i).closed
    · simp [hc] at hs hh
      rw [hA, hB] at hs
      have hsR : ((T.caps i).num : ℝ) * b ≤ ((T.caps i).den : ℝ) *
          (((T.eval i (a+b) - T.eval i a : ℤ) : ℝ) + 1) := by exact_mod_cast hs
      apply (mul_lt_mul_iff_right₀ hdR).mp
      calc
        ((T.caps i).den : ℝ) * ((b : ℝ) * r i) =
            (((T.caps i).den : ℝ) * r i) * b := by ring1
        _ < ((T.caps i).num : ℝ) * b := mul_lt_mul_of_pos_right hh hbR
        _ ≤ _ := hsR
    · simp [hc] at hs hh
      rw [hA, hB] at hs
      have hsR : ((T.caps i).num : ℝ) * b < ((T.caps i).den : ℝ) *
          (((T.eval i (a+b) - T.eval i a : ℤ) : ℝ) + 1) := by exact_mod_cast hs
      apply (mul_lt_mul_iff_right₀ hdR).mp
      calc
        ((T.caps i).den : ℝ) * ((b : ℝ) * r i) =
            (((T.caps i).den : ℝ) * r i) * b := by ring1
        _ ≤ ((T.caps i).num : ℝ) * b := mul_le_mul_of_nonneg_right hh (le_of_lt hbR)
        _ < _ := hsR

end CertifiedDiscovery.Pinwheel
