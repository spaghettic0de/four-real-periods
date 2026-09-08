import CertifiedDiscovery.PinwheelGroups

namespace CertifiedDiscovery.Pinwheel

theorem four_rates_exact (r0 r1 r2 r3 : ℝ)
    (hpos : 0 < r3) (h01 : r1 ≤ r0) (h12 : r2 ≤ r1) (h23 : r3 ≤ r2)
    (hsum : r0+r1+r2+r3 = (5/6 : ℝ)) :
    ∃ F, CumulativeValid (rates r0 r1 r2 r3) F := by
  have hr : ∀ i, 0 ≤ rates r0 r1 r2 r3 i := by
    intro i
    fin_cases i <;> simp [rates] <;> linarith
  rcases four_rate_cover r0 r1 r2 r3 hpos h01 h12 h23 hsum with h | ⟨j, hj, hb⟩
  · rcases h with hA | hB | hC
    · refine ⟨group1 r0, group1_valid r0 r1 r2 r3 r0 hr ?_ ?_ ?_ ?_⟩ <;> linarith
    · refine ⟨group2 (2*r0), group2_valid r0 r1 r2 r3 (2*r0) hr ?_ ?_ ?_ ?_⟩ <;> linarith
    · refine ⟨group3 (3*r0), group3_valid r0 r1 r2 r3 (3*r0) hr ?_ ?_ ?_ ?_⟩ <;> linarith
  · exact periodic_box_valid ⟨j, hj⟩ r0 r1 r2 r3 hb

theorem CumulativeValid.weaken (r s : Fin 4 → ℝ) (F : Fin 4 → ℤ → ℤ)
    (h : CumulativeValid s F) (hrs : ∀ i, r i ≤ s i) : CumulativeValid r F := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro i m L hL
  have hLR : (0 : ℝ) ≤ L := by exact_mod_cast hL
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hrs i) hLR) (h.2.2 i m L hL)

theorem four_rates (r0 r1 r2 r3 : ℝ)
    (hpos : 0 < r3) (h01 : r1 ≤ r0) (h12 : r2 ≤ r1) (h23 : r3 ≤ r2)
    (hsum : r0+r1+r2+r3 ≤ (5/6 : ℝ)) :
    ∃ F, CumulativeValid (rates r0 r1 r2 r3) F := by
  let s0 := (5/6 : ℝ)-r1-r2-r3
  have hs0 : r0 ≤ s0 := by dsimp [s0]; linarith
  obtain ⟨F, hF⟩ := four_rates_exact s0 r1 r2 r3 hpos (by linarith) h12 h23
    (by dsimp [s0]; ring1)
  refine ⟨F, hF.weaken _ _ _ ?_⟩
  intro i
  fin_cases i <;> simp [rates] <;> linarith

#print axioms four_rates
end CertifiedDiscovery.Pinwheel
