import CertifiedDiscovery.PinwheelSchedule

namespace CertifiedDiscovery.Pinwheel

/-- Validity in the period notation used in the original real-period conjecture. -/
def ValidPeriods (a : Fin 4 → ℝ) (S : ℤ → Fin 4) : Prop :=
  ∀ (i : Fin 4) (m : ℤ) (ell : Nat), 0 < ell →
    (ell : ℤ) ≤ scheduleWindowCount S i m ⌈(ell : ℝ) * a i⌉₊

theorem four_periods_schedulable (a0 a1 a2 a3 : ℝ)
    (hpos : 0 < a0) (h01 : a0 ≤ a1) (h12 : a1 ≤ a2) (h23 : a2 ≤ a3)
    (hdensity : 1/a0 + 1/a1 + 1/a2 + 1/a3 ≤ (5/6 : ℝ)) :
    ∃ S : ℤ → Fin 4, ValidPeriods (rates a0 a1 a2 a3) S := by
  have hp1 : 0 < a1 := lt_of_lt_of_le hpos h01
  have hp2 : 0 < a2 := lt_of_lt_of_le hp1 h12
  have hp3 : 0 < a3 := lt_of_lt_of_le hp2 h23
  obtain ⟨S, hS⟩ := four_rates_schedulable (1/a0) (1/a1) (1/a2) (1/a3)
    (one_div_pos.mpr hp3) (one_div_le_one_div_of_le hpos h01)
    (one_div_le_one_div_of_le hp1 h12) (one_div_le_one_div_of_le hp2 h23) hdensity
  refine ⟨S, ?_⟩
  intro i m ell hell
  have hh := hS i m ell hell
  fin_cases i <;> simpa [rates, one_div, div_inv_eq_mul] using hh

#print axioms four_periods_schedulable
end CertifiedDiscovery.Pinwheel
