import CertifiedDiscovery.PinwheelFour

namespace CertifiedDiscovery.Pinwheel

def scheduleOfCounts (F : Fin 4 → ℤ → ℤ) (t : ℤ) : Fin 4 :=
  if F 0 (t+1) - F 0 t = 1 then 0
  else if F 1 (t+1) - F 1 t = 1 then 1
  else if F 2 (t+1) - F 2 t = 1 then 2
  else 3

theorem scheduleOfCounts_indicator (r : Fin 4 → ℝ) (F : Fin 4 → ℤ → ℤ)
    (h : CumulativeValid r F) (i : Fin 4) (t : ℤ) :
    (if scheduleOfCounts F t = i then (1 : ℤ) else 0) = F i (t+1) - F i t := by
  have h0 := h.1 0 t
  have h1 := h.1 1 t
  have h2 := h.1 2 t
  have h3 := h.1 3 t
  have hs := h.2.1 t
  fin_cases i <;> dsimp [scheduleOfCounts] <;> split_ifs <;> norm_num at * <;> omega

/-- Number of executions in the interval [m,m+L), defined without a finite-sum library. -/
def scheduleWindowCount (S : ℤ → Fin 4) (i : Fin 4) (m : ℤ) : Nat → ℤ
  | 0 => 0
  | L+1 => scheduleWindowCount S i m L + if S (m+L) = i then 1 else 0

theorem scheduleWindowCount_eq (r : Fin 4 → ℝ) (F : Fin 4 → ℤ → ℤ)
    (h : CumulativeValid r F) (i : Fin 4) (m : ℤ) (L : Nat) :
    scheduleWindowCount (scheduleOfCounts F) i m L = F i (m+L) - F i m := by
  induction L with
  | zero => simp [scheduleWindowCount]
  | succ L ih =>
    rw [scheduleWindowCount, ih, scheduleOfCounts_indicator r F h]
    push_cast
    simp only [add_assoc]
    omega

/-- The original all-window pinwheel requirement, expressed using positive execution rates. -/
def ValidSchedule (r : Fin 4 → ℝ) (S : ℤ → Fin 4) : Prop :=
  ∀ (i : Fin 4) (m : ℤ) (ell : Nat), 0 < ell →
    (ell : ℤ) ≤ scheduleWindowCount S i m ⌈(ell : ℝ) / r i⌉₊

theorem cumulative_implies_schedule (r : Fin 4 → ℝ) (F : Fin 4 → ℤ → ℤ)
    (h : CumulativeValid r F) (hr : ∀ i, 0 < r i) :
    ValidSchedule r (scheduleOfCounts F) := by
  intro i m ell _
  let L := ⌈(ell : ℝ) / r i⌉₊
  have hreq : (ell : ℝ) ≤ (L : ℝ) * r i :=
    (div_le_iff₀ (hr i)).mp (Nat.le_ceil _)
  rw [scheduleWindowCount_eq r F h]
  apply window_bound_meets_count _ _ (L : ℝ) (r i)
  · simpa only [Int.cast_natCast] using h.2.2 i m (L : ℤ) (Int.natCast_nonneg L)
  · simpa only [Int.cast_natCast] using hreq

theorem four_rates_schedulable (r0 r1 r2 r3 : ℝ)
    (hpos : 0 < r3) (h01 : r1 ≤ r0) (h12 : r2 ≤ r1) (h23 : r3 ≤ r2)
    (hsum : r0+r1+r2+r3 ≤ (5/6 : ℝ)) :
    ∃ S : ℤ → Fin 4, ValidSchedule (rates r0 r1 r2 r3) S := by
  obtain ⟨F, hF⟩ := four_rates r0 r1 r2 r3 hpos h01 h12 h23 hsum
  refine ⟨scheduleOfCounts F, cumulative_implies_schedule _ _ hF ?_⟩
  intro i
  fin_cases i <;> simp [rates] <;> linarith

#print axioms four_rates_schedulable
end CertifiedDiscovery.Pinwheel
