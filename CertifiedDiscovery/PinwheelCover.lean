import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertifiedDiscovery.Pinwheel

def Box (i : Nat) (r0 r1 r2 r3 : ℝ) : Prop :=
  match i with
  | 0 => r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
  | 1 => r0 ≤ (5 / 12 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 ≤ (1 / 6 : ℝ) ∧ r3 < (1 / 6 : ℝ)
  | 2 => r0 < (1 / 3 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 4 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
  | 3 => r0 < (1 / 3 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 4 : ℝ) ∧ r3 < (1 / 7 : ℝ)
  | 4 => r0 < (4 / 7 : ℝ) ∧ r1 < (1 / 6 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
  | 5 => r0 < (7 / 10 : ℝ) ∧ r1 < (1 / 6 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 6 => r0 < (1 / 2 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 7 => r0 < (5 / 13 : ℝ) ∧ r1 < (2 / 7 : ℝ) ∧ r2 < (3 / 14 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 8 => r0 < (10 / 13 : ℝ) ∧ r1 < (1 / 9 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 9 => r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 ≤ (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 10 => r0 < (6 / 11 : ℝ) ∧ r1 < (1 / 5 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 11 => r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 4 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
  | 12 => r0 ≤ (7 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 12 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
  | 13 => r0 < (7 / 16 : ℝ) ∧ r1 < (2 / 7 : ℝ) ∧ r2 < (2 / 13 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 14 => r0 < (3 / 5 : ℝ) ∧ r1 < (2 / 13 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 15 => r0 < (7 / 13 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 16 => r0 ≤ (5 / 9 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 17 => r0 < (4 / 9 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 < (1 / 10 : ℝ)
  | 18 => r0 ≤ (7 / 18 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 < (1 / 9 : ℝ)
  | 19 => r0 < (2 / 3 : ℝ) ∧ r1 < (1 / 6 : ℝ) ∧ r2 < (1 / 10 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 20 => r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
  | 21 => r0 < (3 / 7 : ℝ) ∧ r1 < (3 / 10 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 22 => r0 ≤ (11 / 18 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 23 => r0 < (3 / 7 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 < (3 / 14 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 24 => r0 < (5 / 12 : ℝ) ∧ r1 < (3 / 11 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 25 => r0 < (1 / 2 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 ≤ (1 / 9 : ℝ) ∧ r3 < (1 / 9 : ℝ)
  | 26 => r0 < (7 / 13 : ℝ) ∧ r1 < (1 / 5 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 < (1 / 13 : ℝ)
  | 27 => r0 < (3 / 8 : ℝ) ∧ r1 < (3 / 10 : ℝ) ∧ r2 < (2 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 28 => r0 < (2 / 3 : ℝ) ∧ r1 ≤ (2 / 9 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 29 => r0 < (4 / 9 : ℝ) ∧ r1 < (2 / 7 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 30 => r0 ≤ (13 / 18 : ℝ) ∧ r1 < (1 / 7 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 31 => r0 ≤ (11 / 18 : ℝ) ∧ r1 < (1 / 5 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 32 => r0 ≤ (5 / 9 : ℝ) ∧ r1 ≤ (2 / 9 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 33 => r0 < (2 / 5 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 34 => r0 < (7 / 13 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 35 => r0 < (7 / 16 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 36 => r0 < (7 / 12 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 37 => r0 < (4 / 9 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 38 => r0 < (1 / 2 : ℝ) ∧ r1 < (3 / 14 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 < (1 / 9 : ℝ)
  | 39 => r0 < (3 / 8 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 < (1 / 4 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 40 => r0 < (5 / 9 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 < (1 / 10 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 41 => r0 < (1 / 2 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 42 => r0 < (7 / 13 : ℝ) ∧ r1 < (2 / 11 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 < (1 / 10 : ℝ)
  | 43 => r0 < (1 / 2 : ℝ) ∧ r1 < (3 / 14 : ℝ) ∧ r2 < (3 / 14 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 44 => r0 ≤ (7 / 18 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
  | 45 => r0 < (4 / 11 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 < (1 / 12 : ℝ)
  | 46 => r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 < (1 / 7 : ℝ)
  | _ => False

theorem finite_cover (r0 r1 r2 r3 : ℝ)
    (h0 : r0 + r1 + r2 + r3 ≤ (5 / 6 : ℝ))
    (h1 : -r0 - r1 - r2 - r3 ≤ (-5 / 6 : ℝ))
    (h2 : r1 - r0 ≤ 0) (h3 : r2 - r1 ≤ 0) (h4 : r3 - r2 ≤ 0)
    (h5 : -r3 < 0) (h6 : -r0 - 3*r1 < -1)
    (h7 : -2*r0 - 2*r2 < -1) (h8 : -3*r0 - r3 < -1) :
    ∃ i, i < 47 ∧ Box i r0 r1 r2 r3 := by
  by_cases p272 : r2 < (1 / 7 : ℝ)
  ·
    by_cases p196 : r0 < (4 / 9 : ℝ)
    ·
      by_cases p64 : r2 < (1 / 8 : ℝ)
      ·
        by_cases p42 : r1 < (1 / 4 : ℝ)
        ·
          by_cases p30 : r1 ≤ (2 / 9 : ℝ)
          ·
            by_cases p24 : r0 < (7 / 16 : ℝ)
            ·
              by_cases p20 : r1 < (2 / 9 : ℝ)
              ·
                by_cases p14 : r2 ≤ (1 / 9 : ℝ)
                ·
                  by_cases p4 : r3 ≤ (1 / 18 : ℝ)
                  ·
                    exfalso
                    linarith only [h1, p30, p24, p14, p4]
                  ·
                    have p4n : -r3 < -(1 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p4)
                    by_cases p3 : r0 ≤ (5 / 12 : ℝ)
                    ·
                      refine ⟨1, by decide, ?_⟩
                      change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 ≤ (1 / 6 : ℝ) ∧ r3 < (1 / 6 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p3]
                      · linarith only [p20]
                      · linarith only [p14]
                      · linarith only [h4, p14]
                    ·
                      have p3n : -r0 < -(5 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p3)
                      refine ⟨25, by decide, ?_⟩
                      change r0 < (1 / 2 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 ≤ (1 / 9 : ℝ) ∧ r3 < (1 / 9 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p24]
                      · linarith only [p30]
                      · linarith only [p14]
                      · linarith only [h0, h4, h6, p3n]
                ·
                  have p14n : -r2 < -(1 / 9 : ℝ) := neg_lt_neg (lt_of_not_ge p14)
                  by_cases p13 : r0 < (3 / 7 : ℝ)
                  ·
                    by_cases p9 : r0 ≤ (5 / 12 : ℝ)
                    ·
                      refine ⟨1, by decide, ?_⟩
                      change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 ≤ (1 / 6 : ℝ) ∧ r3 < (1 / 6 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p9]
                      · linarith only [p20]
                      · linarith only [p64]
                      · linarith only [h0, h4, h6, h7]
                    ·
                      have p9n : -r0 < -(5 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p9)
                      by_cases p8 : r1 < (3 / 14 : ℝ)
                      ·
                        refine ⟨38, by decide, ?_⟩
                        change r0 < (1 / 2 : ℝ) ∧ r1 < (3 / 14 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 < (1 / 9 : ℝ)
                        refine ⟨?_, ?_, ?_, ?_⟩
                        · linarith only [p13]
                        · linarith only [p8]
                        · linarith only [p64]
                        · linarith only [h0, h6, p14n, p9n]
                      ·
                        have p8n : -r1 ≤ -(3 / 14 : ℝ) := neg_le_neg (le_of_not_gt p8)
                        refine ⟨17, by decide, ?_⟩
                        change r0 < (4 / 9 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 < (1 / 10 : ℝ)
                        refine ⟨?_, ?_, ?_, ?_⟩
                        · linarith only [p13]
                        · linarith only [p30]
                        · linarith only [p64]
                        · linarith only [h0, p14n, p9n, p8n]
                  ·
                    have p13n : -r0 ≤ -(3 / 7 : ℝ) := neg_le_neg (le_of_not_gt p13)
                    by_cases p12 : r1 < (3 / 14 : ℝ)
                    ·
                      refine ⟨38, by decide, ?_⟩
                      change r0 < (1 / 2 : ℝ) ∧ r1 < (3 / 14 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 < (1 / 9 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p24]
                      · linarith only [p12]
                      · linarith only [p64]
                      · linarith only [h0, h6, p14n, p13n]
                    ·
                      have p12n : -r1 ≤ -(3 / 14 : ℝ) := neg_le_neg (le_of_not_gt p12)
                      refine ⟨17, by decide, ?_⟩
                      change r0 < (4 / 9 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 < (1 / 10 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p24]
                      · linarith only [p30]
                      · linarith only [p64]
                      · linarith only [h0, p14n, p13n, p12n]
              ·
                have p20n : -r1 ≤ -(2 / 9 : ℝ) := neg_le_neg (le_of_not_gt p20)
                by_cases p19 : r0 < (3 / 7 : ℝ)
                ·
                  by_cases p17 : r0 ≤ (5 / 12 : ℝ)
                  ·
                    refine ⟨46, by decide, ?_⟩
                    change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 < (1 / 7 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [p17]
                    · linarith only [p30]
                    · linarith only [p64]
                    · linarith only [h0, h7, p20n]
                  ·
                    have p17n : -r0 < -(5 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p17)
                    refine ⟨17, by decide, ?_⟩
                    change r0 < (4 / 9 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 < (1 / 10 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [p19]
                    · linarith only [p30]
                    · linarith only [p64]
                    · linarith only [h0, h4, p20n, p17n]
                ·
                  have p19n : -r0 ≤ -(3 / 7 : ℝ) := neg_le_neg (le_of_not_gt p19)
                  refine ⟨17, by decide, ?_⟩
                  change r0 < (4 / 9 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 < (1 / 10 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p24]
                  · linarith only [p30]
                  · linarith only [p64]
                  · linarith only [h0, h4, p20n, p19n]
            ·
              have p24n : -r0 ≤ -(7 / 16 : ℝ) := neg_le_neg (le_of_not_gt p24)
              by_cases p23 : r2 ≤ (1 / 9 : ℝ)
              ·
                refine ⟨25, by decide, ?_⟩
                change r0 < (1 / 2 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 ≤ (1 / 9 : ℝ) ∧ r3 < (1 / 9 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [p196]
                · linarith only [p30]
                · linarith only [p23]
                · linarith only [h0, h4, h6, p24n]
              ·
                have p23n : -r2 < -(1 / 9 : ℝ) := neg_lt_neg (lt_of_not_ge p23)
                refine ⟨17, by decide, ?_⟩
                change r0 < (4 / 9 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 < (1 / 10 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [p196]
                · linarith only [p30]
                · linarith only [p64]
                · linarith only [h0, h6, p24n, p23n]
          ·
            have p30n : -r1 < -(2 / 9 : ℝ) := neg_lt_neg (lt_of_not_ge p30)
            by_cases p29 : r0 < (3 / 7 : ℝ)
            ·
              by_cases p27 : r0 ≤ (5 / 12 : ℝ)
              ·
                refine ⟨46, by decide, ?_⟩
                change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 < (1 / 7 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [p27]
                · linarith only [p42]
                · linarith only [p64]
                · linarith only [h0, h7, p30n]
              ·
                have p27n : -r0 < -(5 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p27)
                refine ⟨17, by decide, ?_⟩
                change r0 < (4 / 9 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 < (1 / 10 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [p29]
                · linarith only [p42]
                · linarith only [p64]
                · linarith only [h0, h4, p30n, p27n]
            ·
              have p29n : -r0 ≤ -(3 / 7 : ℝ) := neg_le_neg (le_of_not_gt p29)
              refine ⟨17, by decide, ?_⟩
              change r0 < (4 / 9 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 < (1 / 10 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p196]
              · linarith only [p42]
              · linarith only [p64]
              · linarith only [h0, h4, p30n, p29n]
        ·
          have p42n : -r1 ≤ -(1 / 4 : ℝ) := neg_le_neg (le_of_not_gt p42)
          by_cases p41 : r0 ≤ (5 / 12 : ℝ)
          ·
            refine ⟨0, by decide, ?_⟩
            change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
            refine ⟨?_, ?_, ?_, ?_⟩
            · linarith only [p41]
            · linarith only [h0, h5, h7]
            · linarith only [p64]
            · linarith only [h0, h7, p42n]
          ·
            have p41n : -r0 < -(5 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p41)
            by_cases p40 : r2 ≤ (1 / 9 : ℝ)
            ·
              by_cases p36 : r1 < (2 / 7 : ℝ)
              ·
                by_cases p34 : r1 ≤ (5 / 18 : ℝ)
                ·
                  refine ⟨25, by decide, ?_⟩
                  change r0 < (1 / 2 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 ≤ (1 / 9 : ℝ) ∧ r3 < (1 / 9 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p196]
                  · linarith only [p34]
                  · linarith only [p40]
                  · linarith only [h0, h4, p42n, p41n]
                ·
                  have p34n : -r1 < -(5 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p34)
                  refine ⟨9, by decide, ?_⟩
                  change r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 ≤ (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p196]
                  · linarith only [p36]
                  · linarith only [p40]
                  · linarith only [h0, h7, p34n]
              ·
                have p36n : -r1 ≤ -(2 / 7 : ℝ) := neg_le_neg (le_of_not_gt p36)
                refine ⟨9, by decide, ?_⟩
                change r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 ≤ (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [p196]
                · linarith only [h0, h5, h7]
                · linarith only [p40]
                · linarith only [h0, h7, p36n]
            ·
              have p40n : -r2 < -(1 / 9 : ℝ) := neg_lt_neg (lt_of_not_ge p40)
              by_cases p39 : r0 < (7 / 16 : ℝ)
              ·
                refine ⟨35, by decide, ?_⟩
                change r0 < (7 / 16 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [p39]
                · linarith only [h0, h5, p41n, p40n]
                · linarith only [p64]
                · linarith only [h0, p42n, p41n, p40n]
              ·
                have p39n : -r0 ≤ -(7 / 16 : ℝ) := neg_le_neg (le_of_not_gt p39)
                refine ⟨29, by decide, ?_⟩
                change r0 < (4 / 9 : ℝ) ∧ r1 < (2 / 7 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [p196]
                · linarith only [h0, h5, p40n, p39n]
                · linarith only [p64]
                · linarith only [h0, p42n, p40n, p39n]
      ·
        have p64n : -r2 ≤ -(1 / 8 : ℝ) := neg_le_neg (le_of_not_gt p64)
        by_cases p63 : r0 ≤ (5 / 12 : ℝ)
        ·
          by_cases p49 : r0 < (5 / 12 : ℝ)
          ·
            by_cases p45 : r1 < (1 / 4 : ℝ)
            ·
              refine ⟨46, by decide, ?_⟩
              change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 < (1 / 7 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p49]
              · linarith only [p45]
              · linarith only [p272]
              · linarith only [h0, h4, h6, h7]
            ·
              have p45n : -r1 ≤ -(1 / 4 : ℝ) := neg_le_neg (le_of_not_gt p45)
              refine ⟨0, by decide, ?_⟩
              change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p49]
              · linarith only [h0, h5, h7]
              · linarith only [p272]
              · linarith only [h0, h7, p45n]
          ·
            have p49n : -r0 ≤ -(5 / 12 : ℝ) := neg_le_neg (le_of_not_gt p49)
            by_cases p48 : r1 < (2 / 9 : ℝ)
            ·
              refine ⟨1, by decide, ?_⟩
              change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 ≤ (1 / 6 : ℝ) ∧ r3 < (1 / 6 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p63]
              · linarith only [p48]
              · linarith only [p272]
              · linarith only [h0, h4, h6, p49n]
            ·
              have p48n : -r1 ≤ -(2 / 9 : ℝ) := neg_le_neg (le_of_not_gt p48)
              refine ⟨0, by decide, ?_⟩
              change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p63]
              · linarith only [h0, h5, p64n, p49n]
              · linarith only [p272]
              · linarith only [h0, p64n, p49n, p48n]
        ·
          have p63n : -r0 < -(5 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p63)
          by_cases p62 : r1 < (2 / 9 : ℝ)
          ·
            by_cases p52 : r1 < (3 / 14 : ℝ)
            ·
              refine ⟨38, by decide, ?_⟩
              change r0 < (1 / 2 : ℝ) ∧ r1 < (3 / 14 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 < (1 / 9 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p196]
              · linarith only [p52]
              · linarith only [p272]
              · linarith only [h0, h6, p64n, p63n]
            ·
              have p52n : -r1 ≤ -(3 / 14 : ℝ) := neg_le_neg (le_of_not_gt p52)
              refine ⟨20, by decide, ?_⟩
              change r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p196]
              · linarith only [p62]
              · linarith only [p272]
              · linarith only [h0, p64n, p63n, p52n]
          ·
            have p62n : -r1 ≤ -(2 / 9 : ℝ) := neg_le_neg (le_of_not_gt p62)
            by_cases p61 : r0 < (7 / 16 : ℝ)
            ·
              by_cases p59 : r1 ≤ (5 / 18 : ℝ)
              ·
                by_cases p55 : r1 < (1 / 4 : ℝ)
                ·
                  refine ⟨20, by decide, ?_⟩
                  change r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p61]
                  · linarith only [p55]
                  · linarith only [p272]
                  · linarith only [h0, p64n, p63n, p62n]
                ·
                  have p55n : -r1 ≤ -(1 / 4 : ℝ) := neg_le_neg (le_of_not_gt p55)
                  refine ⟨13, by decide, ?_⟩
                  change r0 < (7 / 16 : ℝ) ∧ r1 < (2 / 7 : ℝ) ∧ r2 < (2 / 13 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p61]
                  · linarith only [p59]
                  · linarith only [p272]
                  · linarith only [h0, p64n, p63n, p55n]
              ·
                have p59n : -r1 < -(5 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p59)
                by_cases p58 : r0 < (3 / 7 : ℝ)
                ·
                  refine ⟨21, by decide, ?_⟩
                  change r0 < (3 / 7 : ℝ) ∧ r1 < (3 / 10 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p58]
                  · linarith only [h0, h5, p64n, p63n]
                  · linarith only [h0, h5, p63n, p59n]
                  · linarith only [h0, p64n, p63n, p59n]
                ·
                  have p58n : -r0 ≤ -(3 / 7 : ℝ) := neg_le_neg (le_of_not_gt p58)
                  refine ⟨13, by decide, ?_⟩
                  change r0 < (7 / 16 : ℝ) ∧ r1 < (2 / 7 : ℝ) ∧ r2 < (2 / 13 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [h0, h5, p64n, p59n]
                  · linarith only [h0, h5, p64n, p58n]
                  · linarith only [p272]
                  · linarith only [h0, p64n, p59n, p58n]
            ·
              have p61n : -r0 ≤ -(7 / 16 : ℝ) := neg_le_neg (le_of_not_gt p61)
              refine ⟨41, by decide, ?_⟩
              change r0 < (1 / 2 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p196]
              · linarith only [h0, h5, p64n, p61n]
              · linarith only [p272]
              · linarith only [h0, p64n, p62n, p61n]
    ·
      have p196n : -r0 ≤ -(4 / 9 : ℝ) := neg_le_neg (le_of_not_gt p196)
      by_cases p195 : r0 < (6 / 11 : ℝ)
      ·
        by_cases p141 : r1 < (3 / 14 : ℝ)
        ·
          by_cases p99 : r0 < (7 / 13 : ℝ)
          ·
            by_cases p91 : r2 < (1 / 10 : ℝ)
            ·
              by_cases p79 : r1 < (1 / 5 : ℝ)
              ·
                by_cases p71 : r2 ≤ (1 / 12 : ℝ)
                ·
                  refine ⟨12, by decide, ?_⟩
                  change r0 ≤ (7 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 12 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p99]
                  · linarith only [p79]
                  · linarith only [p71]
                  · linarith only [h4, p71]
                ·
                  have p71n : -r2 < -(1 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p71)
                  by_cases p70 : r0 < (1 / 2 : ℝ)
                  ·
                    refine ⟨25, by decide, ?_⟩
                    change r0 < (1 / 2 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 ≤ (1 / 9 : ℝ) ∧ r3 < (1 / 9 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [p70]
                    · linarith only [p79]
                    · linarith only [p91]
                    · linarith only [h4, p91]
                  ·
                    have p70n : -r0 ≤ -(1 / 2 : ℝ) := neg_le_neg (le_of_not_gt p70)
                    by_cases p69 : r1 < (2 / 11 : ℝ)
                    ·
                      refine ⟨42, by decide, ?_⟩
                      change r0 < (7 / 13 : ℝ) ∧ r1 < (2 / 11 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 < (1 / 10 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p99]
                      · linarith only [p69]
                      · linarith only [p91]
                      · linarith only [h0, h4, h6, p70n]
                    ·
                      have p69n : -r1 ≤ -(2 / 11 : ℝ) := neg_le_neg (le_of_not_gt p69)
                      refine ⟨26, by decide, ?_⟩
                      change r0 < (7 / 13 : ℝ) ∧ r1 < (1 / 5 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 < (1 / 13 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p99]
                      · linarith only [p79]
                      · linarith only [p91]
                      · linarith only [h0, p71n, p70n, p69n]
              ·
                have p79n : -r1 ≤ -(1 / 5 : ℝ) := neg_le_neg (le_of_not_gt p79)
                by_cases p78 : r0 < (1 / 2 : ℝ)
                ·
                  refine ⟨25, by decide, ?_⟩
                  change r0 < (1 / 2 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 ≤ (1 / 9 : ℝ) ∧ r3 < (1 / 9 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p78]
                  · linarith only [p141]
                  · linarith only [p91]
                  · linarith only [h0, h4, p196n, p79n]
                ·
                  have p78n : -r0 ≤ -(1 / 2 : ℝ) := neg_le_neg (le_of_not_gt p78)
                  by_cases p77 : r2 ≤ (1 / 18 : ℝ)
                  ·
                    refine ⟨12, by decide, ?_⟩
                    change r0 ≤ (7 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 12 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [p99]
                    · linarith only [p141]
                    · linarith only [p77]
                    · linarith only [h4, p77]
                  ·
                    have p77n : -r2 < -(1 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p77)
                    by_cases p76 : r2 ≤ (1 / 12 : ℝ)
                    ·
                      refine ⟨12, by decide, ?_⟩
                      change r0 ≤ (7 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 12 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p99]
                      · linarith only [p141]
                      · linarith only [p76]
                      · linarith only [h0, h4, p79n, p78n]
                    ·
                      have p76n : -r2 < -(1 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p76)
                      refine ⟨15, by decide, ?_⟩
                      change r0 < (7 / 13 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p99]
                      · linarith only [p141]
                      · linarith only [p91]
                      · linarith only [h0, p79n, p78n, p76n]
            ·
              have p91n : -r2 ≤ -(1 / 10 : ℝ) := neg_le_neg (le_of_not_gt p91)
              by_cases p90 : r2 < (1 / 8 : ℝ)
              ·
                by_cases p86 : r0 < (1 / 2 : ℝ)
                ·
                  refine ⟨38, by decide, ?_⟩
                  change r0 < (1 / 2 : ℝ) ∧ r1 < (3 / 14 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 < (1 / 9 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p86]
                  · linarith only [p141]
                  · linarith only [p90]
                  · linarith only [h0, h4, h6, p196n]
                ·
                  have p86n : -r0 ≤ -(1 / 2 : ℝ) := neg_le_neg (le_of_not_gt p86)
                  by_cases p85 : r2 < (1 / 9 : ℝ)
                  ·
                    by_cases p83 : r1 < (2 / 11 : ℝ)
                    ·
                      refine ⟨26, by decide, ?_⟩
                      change r0 < (7 / 13 : ℝ) ∧ r1 < (1 / 5 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 < (1 / 13 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p99]
                      · linarith only [p83]
                      · linarith only [p85]
                      · linarith only [h0, h6, p91n, p86n]
                    ·
                      have p83n : -r1 ≤ -(2 / 11 : ℝ) := neg_le_neg (le_of_not_gt p83)
                      refine ⟨15, by decide, ?_⟩
                      change r0 < (7 / 13 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p99]
                      · linarith only [p141]
                      · linarith only [p85]
                      · linarith only [h0, p91n, p86n, p83n]
                  ·
                    have p85n : -r2 ≤ -(1 / 9 : ℝ) := neg_le_neg (le_of_not_gt p85)
                    refine ⟨32, by decide, ?_⟩
                    change r0 ≤ (5 / 9 : ℝ) ∧ r1 ≤ (2 / 9 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [p99]
                    · linarith only [p141]
                    · linarith only [p90]
                    · linarith only [h0, h6, p86n, p85n]
              ·
                have p90n : -r2 ≤ -(1 / 8 : ℝ) := neg_le_neg (le_of_not_gt p90)
                by_cases p89 : r0 < (1 / 2 : ℝ)
                ·
                  refine ⟨20, by decide, ?_⟩
                  change r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p89]
                  · linarith only [p141]
                  · linarith only [p272]
                  · linarith only [h0, h6, p196n, p90n]
                ·
                  have p89n : -r0 ≤ -(1 / 2 : ℝ) := neg_le_neg (le_of_not_gt p89)
                  refine ⟨34, by decide, ?_⟩
                  change r0 < (7 / 13 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p99]
                  · linarith only [p141]
                  · linarith only [p272]
                  · linarith only [h0, h6, p90n, p89n]
          ·
            have p99n : -r0 ≤ -(7 / 13 : ℝ) := neg_le_neg (le_of_not_gt p99)
            by_cases p98 : r2 ≤ (1 / 12 : ℝ)
            ·
              refine ⟨12, by decide, ?_⟩
              change r0 ≤ (7 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 12 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p195]
              · linarith only [p141]
              · linarith only [p98]
              · linarith only [h0, h4, h6, p99n]
            ·
              have p98n : -r2 < -(1 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p98)
              by_cases p97 : r2 < (1 / 9 : ℝ)
              ·
                by_cases p95 : r1 < (1 / 6 : ℝ)
                ·
                  refine ⟨4, by decide, ?_⟩
                  change r0 < (4 / 7 : ℝ) ∧ r1 < (1 / 6 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p195]
                  · linarith only [p95]
                  · linarith only [p97]
                  · linarith only [h0, h6, p99n, p98n]
                ·
                  have p95n : -r1 ≤ -(1 / 6 : ℝ) := neg_le_neg (le_of_not_gt p95)
                  refine ⟨32, by decide, ?_⟩
                  change r0 ≤ (5 / 9 : ℝ) ∧ r1 ≤ (2 / 9 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p195]
                  · linarith only [p141]
                  · linarith only [p97]
                  · linarith only [h0, p99n, p98n, p95n]
              ·
                have p97n : -r2 ≤ -(1 / 9 : ℝ) := neg_le_neg (le_of_not_gt p97)
                refine ⟨10, by decide, ?_⟩
                change r0 < (6 / 11 : ℝ) ∧ r1 < (1 / 5 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [p195]
                · linarith only [h0, h5, p99n, p97n]
                · linarith only [p272]
                · linarith only [h0, h6, p99n, p97n]
        ·
          have p141n : -r1 ≤ -(3 / 14 : ℝ) := neg_le_neg (le_of_not_gt p141)
          by_cases p140 : r0 < (7 / 13 : ℝ)
          ·
            by_cases p136 : r2 < (1 / 10 : ℝ)
            ·
              by_cases p120 : r1 < (1 / 4 : ℝ)
              ·
                by_cases p110 : r0 < (1 / 2 : ℝ)
                ·
                  refine ⟨25, by decide, ?_⟩
                  change r0 < (1 / 2 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 ≤ (1 / 9 : ℝ) ∧ r3 < (1 / 9 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p110]
                  · linarith only [p120]
                  · linarith only [p136]
                  · linarith only [h0, h4, p196n, p141n]
                ·
                  have p110n : -r0 ≤ -(1 / 2 : ℝ) := neg_le_neg (le_of_not_gt p110)
                  by_cases p109 : r2 ≤ (1 / 18 : ℝ)
                  ·
                    refine ⟨12, by decide, ?_⟩
                    change r0 ≤ (7 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 12 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [p140]
                    · linarith only [p120]
                    · linarith only [p109]
                    · linarith only [h4, p109]
                  ·
                    have p109n : -r2 < -(1 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p109)
                    by_cases p108 : r1 ≤ (2 / 9 : ℝ)
                    ·
                      by_cases p106 : r1 < (2 / 9 : ℝ)
                      ·
                        by_cases p104 : r2 ≤ (1 / 12 : ℝ)
                        ·
                          refine ⟨12, by decide, ?_⟩
                          change r0 ≤ (7 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 12 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                          refine ⟨?_, ?_, ?_, ?_⟩
                          · linarith only [p140]
                          · linarith only [p108]
                          · linarith only [p104]
                          · linarith only [h0, h4, p141n, p110n]
                        ·
                          have p104n : -r2 < -(1 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p104)
                          refine ⟨15, by decide, ?_⟩
                          change r0 < (7 / 13 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                          refine ⟨?_, ?_, ?_, ?_⟩
                          · linarith only [h0, h5, p141n, p104n]
                          · linarith only [p108]
                          · linarith only [p136]
                          · linarith only [h0, p141n, p110n, p104n]
                      ·
                        have p106n : -r1 ≤ -(2 / 9 : ℝ) := neg_le_neg (le_of_not_gt p106)
                        refine ⟨15, by decide, ?_⟩
                        change r0 < (7 / 13 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                        refine ⟨?_, ?_, ?_, ?_⟩
                        · linarith only [p140]
                        · linarith only [p108]
                        · linarith only [p136]
                        · linarith only [h0, p110n, p109n, p106n]
                    ·
                      have p108n : -r1 < -(2 / 9 : ℝ) := neg_lt_neg (lt_of_not_ge p108)
                      refine ⟨15, by decide, ?_⟩
                      change r0 < (7 / 13 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p140]
                      · linarith only [p120]
                      · linarith only [p136]
                      · linarith only [h0, p110n, p109n, p108n]
              ·
                have p120n : -r1 ≤ -(1 / 4 : ℝ) := neg_le_neg (le_of_not_gt p120)
                by_cases p119 : r0 < (1 / 2 : ℝ)
                ·
                  by_cases p115 : r2 ≤ (1 / 18 : ℝ)
                  ·
                    refine ⟨9, by decide, ?_⟩
                    change r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 ≤ (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [p119]
                    · linarith only [h0, h5, h7]
                    · linarith only [p115]
                    · linarith only [h4, p115]
                  ·
                    have p115n : -r2 < -(1 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p115)
                    by_cases p114 : r3 ≤ (1 / 18 : ℝ)
                    ·
                      refine ⟨9, by decide, ?_⟩
                      change r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 ≤ (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p119]
                      · linarith only [h0, h5, h7]
                      · linarith only [p136]
                      · linarith only [p114]
                    ·
                      have p114n : -r3 < -(1 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p114)
                      refine ⟨25, by decide, ?_⟩
                      change r0 < (1 / 2 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 ≤ (1 / 9 : ℝ) ∧ r3 < (1 / 9 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [h0, p120n, p115n, p114n]
                      · linarith only [h0, h7, p114n]
                      · linarith only [p136]
                      · linarith only [h0, h4, p196n, p120n]
                ·
                  have p119n : -r0 ≤ -(1 / 2 : ℝ) := neg_le_neg (le_of_not_gt p119)
                  by_cases p118 : r2 ≤ (1 / 18 : ℝ)
                  ·
                    refine ⟨16, by decide, ?_⟩
                    change r0 ≤ (5 / 9 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [p140]
                    · linarith only [h0, h5, h7]
                    · linarith only [p118]
                    · linarith only [h0, h4, p120n, p119n]
                  ·
                    have p118n : -r2 < -(1 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p118)
                    refine ⟨40, by decide, ?_⟩
                    change r0 < (5 / 9 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 < (1 / 10 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [p140]
                    · linarith only [h0, h5, p119n, p118n]
                    · linarith only [h0, h5, p120n, p119n]
                    · linarith only [h0, p120n, p119n, p118n]
            ·
              have p136n : -r2 ≤ -(1 / 10 : ℝ) := neg_le_neg (le_of_not_gt p136)
              by_cases p135 : r2 < (1 / 8 : ℝ)
              ·
                by_cases p133 : r2 ≤ (1 / 9 : ℝ)
                ·
                  by_cases p127 : r0 < (1 / 2 : ℝ)
                  ·
                    by_cases p123 : r1 < (1 / 4 : ℝ)
                    ·
                      refine ⟨20, by decide, ?_⟩
                      change r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p127]
                      · linarith only [p123]
                      · linarith only [p133]
                      · linarith only [h0, p196n, p141n, p136n]
                    ·
                      have p123n : -r1 ≤ -(1 / 4 : ℝ) := neg_le_neg (le_of_not_gt p123)
                      refine ⟨9, by decide, ?_⟩
                      change r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 ≤ (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [h0, h5, p136n, p123n]
                      · linarith only [h0, h5, p196n, p136n]
                      · linarith only [p133]
                      · linarith only [h0, p196n, p136n, p123n]
                  ·
                    have p127n : -r0 ≤ -(1 / 2 : ℝ) := neg_le_neg (le_of_not_gt p127)
                    by_cases p126 : r1 ≤ (2 / 9 : ℝ)
                    ·
                      refine ⟨32, by decide, ?_⟩
                      change r0 ≤ (5 / 9 : ℝ) ∧ r1 ≤ (2 / 9 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p140]
                      · linarith only [p126]
                      · linarith only [p133]
                      · linarith only [h0, p141n, p136n, p127n]
                    ·
                      have p126n : -r1 < -(2 / 9 : ℝ) := neg_lt_neg (lt_of_not_ge p126)
                      refine ⟨15, by decide, ?_⟩
                      change r0 < (7 / 13 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [h0, h5, p136n, p126n]
                      · linarith only [h0, h5, p136n, p127n]
                      · linarith only [h0, h5, p127n, p126n]
                      · linarith only [h0, p136n, p127n, p126n]
                ·
                  have p133n : -r2 < -(1 / 9 : ℝ) := neg_lt_neg (lt_of_not_ge p133)
                  by_cases p132 : r0 < (1 / 2 : ℝ)
                  ·
                    by_cases p130 : r1 ≤ (2 / 9 : ℝ)
                    ·
                      refine ⟨20, by decide, ?_⟩
                      change r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p132]
                      · linarith only [p130]
                      · linarith only [p135]
                      · linarith only [h0, p196n, p141n, p133n]
                    ·
                      have p130n : -r1 < -(2 / 9 : ℝ) := neg_lt_neg (lt_of_not_ge p130)
                      refine ⟨41, by decide, ?_⟩
                      change r0 < (1 / 2 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [h0, h5, p133n, p130n]
                      · linarith only [h0, h5, p196n, p133n]
                      · linarith only [p135]
                      · linarith only [h0, p196n, p133n, p130n]
                  ·
                    have p132n : -r0 ≤ -(1 / 2 : ℝ) := neg_le_neg (le_of_not_gt p132)
                    refine ⟨32, by decide, ?_⟩
                    change r0 ≤ (5 / 9 : ℝ) ∧ r1 ≤ (2 / 9 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [h0, h5, p141n, p133n]
                    · linarith only [h0, h5, p133n, p132n]
                    · linarith only [h0, h5, p141n, p132n]
                    · linarith only [h0, p141n, p133n, p132n]
              ·
                have p135n : -r2 ≤ -(1 / 8 : ℝ) := neg_le_neg (le_of_not_gt p135)
                refine ⟨41, by decide, ?_⟩
                change r0 < (1 / 2 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [h0, h5, p141n, p135n]
                · linarith only [h0, h5, p196n, p135n]
                · linarith only [p272]
                · linarith only [h0, p196n, p141n, p135n]
          ·
            have p140n : -r0 ≤ -(7 / 13 : ℝ) := neg_le_neg (le_of_not_gt p140)
            by_cases p139 : r2 ≤ (1 / 18 : ℝ)
            ·
              refine ⟨16, by decide, ?_⟩
              change r0 ≤ (5 / 9 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p195]
              · linarith only [h0, h4, h5, p140n]
              · linarith only [p139]
              · linarith only [h0, h4, p141n, p140n]
            ·
              have p139n : -r2 < -(1 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p139)
              refine ⟨12, by decide, ?_⟩
              change r0 ≤ (7 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 12 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p195]
              · linarith only [h0, h5, p140n, p139n]
              · linarith only [h0, h5, p141n, p140n]
              · linarith only [h0, h4, p141n, p140n]
      ·
        have p195n : -r0 ≤ -(6 / 11 : ℝ) := neg_le_neg (le_of_not_gt p195)
        by_cases p194 : r2 ≤ (1 / 18 : ℝ)
        ·
          by_cases p162 : r1 < (1 / 5 : ℝ)
          ·
            by_cases p150 : r0 < (3 / 5 : ℝ)
            ·
              refine ⟨22, by decide, ?_⟩
              change r0 ≤ (11 / 18 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p150]
              · linarith only [p162]
              · linarith only [p194]
              · linarith only [h4, p194]
            ·
              have p150n : -r0 ≤ -(3 / 5 : ℝ) := neg_le_neg (le_of_not_gt p150)
              by_cases p149 : r0 < (2 / 3 : ℝ)
              ·
                refine ⟨28, by decide, ?_⟩
                change r0 < (2 / 3 : ℝ) ∧ r1 ≤ (2 / 9 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [p149]
                · linarith only [p162]
                · linarith only [p194]
                · linarith only [h0, h4, h6, p150n]
              ·
                have p149n : -r0 ≤ -(2 / 3 : ℝ) := neg_le_neg (le_of_not_gt p149)
                by_cases p148 : r1 < (1 / 9 : ℝ)
                ·
                  refine ⟨8, by decide, ?_⟩
                  change r0 < (10 / 13 : ℝ) ∧ r1 < (1 / 9 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [h0, h4, h5, h6]
                  · linarith only [p148]
                  · linarith only [h0, h5, h6, p148]
                  · linarith only [h0, h4, h6, p149n]
                ·
                  have p148n : -r1 ≤ -(1 / 9 : ℝ) := neg_le_neg (le_of_not_gt p148)
                  by_cases p147 : r1 < (1 / 7 : ℝ)
                  ·
                    refine ⟨30, by decide, ?_⟩
                    change r0 ≤ (13 / 18 : ℝ) ∧ r1 < (1 / 7 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [h0, h4, h5, p148n]
                    · linarith only [p147]
                    · linarith only [h0, h5, h6, p149n]
                    · linarith only [h0, h4, h6, p149n]
                  ·
                    have p147n : -r1 ≤ -(1 / 7 : ℝ) := neg_le_neg (le_of_not_gt p147)
                    refine ⟨5, by decide, ?_⟩
                    change r0 < (7 / 10 : ℝ) ∧ r1 < (1 / 6 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [h0, h4, h5, p147n]
                    · linarith only [h0, h4, h5, p149n]
                    · linarith only [h0, h5, p149n, p147n]
                    · linarith only [h0, h4, p149n, p147n]
          ·
            have p162n : -r1 ≤ -(1 / 5 : ℝ) := neg_le_neg (le_of_not_gt p162)
            by_cases p161 : r1 < (1 / 4 : ℝ)
            ·
              by_cases p157 : r0 ≤ (5 / 9 : ℝ)
              ·
                refine ⟨12, by decide, ?_⟩
                change r0 ≤ (7 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 12 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [p157]
                · linarith only [p161]
                · linarith only [p194]
                · linarith only [h0, h4, p195n, p162n]
              ·
                have p157n : -r0 < -(5 / 9 : ℝ) := neg_lt_neg (lt_of_not_ge p157)
                by_cases p156 : r0 ≤ (7 / 12 : ℝ)
                ·
                  refine ⟨12, by decide, ?_⟩
                  change r0 ≤ (7 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 12 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p156]
                  · linarith only [p161]
                  · linarith only [p194]
                  · linarith only [h0, h4, p162n, p157n]
                ·
                  have p156n : -r0 < -(7 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p156)
                  by_cases p155 : r1 ≤ (2 / 9 : ℝ)
                  ·
                    refine ⟨28, by decide, ?_⟩
                    change r0 < (2 / 3 : ℝ) ∧ r1 ≤ (2 / 9 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [h0, h4, h5, p162n]
                    · linarith only [p155]
                    · linarith only [h0, h5, p162n, p156n]
                    · linarith only [h0, h4, p162n, p156n]
                  ·
                    have p155n : -r1 < -(2 / 9 : ℝ) := neg_lt_neg (lt_of_not_ge p155)
                    refine ⟨22, by decide, ?_⟩
                    change r0 ≤ (11 / 18 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [h0, h4, h5, p155n]
                    · linarith only [h0, h4, h5, p156n]
                    · linarith only [h0, h5, p156n, p155n]
                    · linarith only [h0, h4, p156n, p155n]
            ·
              have p161n : -r1 ≤ -(1 / 4 : ℝ) := neg_le_neg (le_of_not_gt p161)
              by_cases p160 : r1 ≤ (5 / 18 : ℝ)
              ·
                refine ⟨36, by decide, ?_⟩
                change r0 < (7 / 12 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [h0, h4, h5, p161n]
                · linarith only [p160]
                · linarith only [h0, h5, p195n, p161n]
                · linarith only [h0, h4, p195n, p161n]
              ·
                have p160n : -r1 < -(5 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p160)
                refine ⟨16, by decide, ?_⟩
                change r0 ≤ (5 / 9 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 ≤ (1 / 18 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [h0, h4, h5, p160n]
                · linarith only [h0, h4, h5, p195n]
                · linarith only [h0, h5, p195n, p160n]
                · linarith only [h0, h4, p195n, p160n]
        ·
          have p194n : -r2 < -(1 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p194)
          by_cases p193 : r2 < (1 / 10 : ℝ)
          ·
            by_cases p181 : r1 < (1 / 5 : ℝ)
            ·
              by_cases p177 : r1 < (1 / 6 : ℝ)
              ·
                by_cases p169 : r0 ≤ (7 / 12 : ℝ)
                ·
                  by_cases p167 : r0 < (4 / 7 : ℝ)
                  ·
                    refine ⟨4, by decide, ?_⟩
                    change r0 < (4 / 7 : ℝ) ∧ r1 < (1 / 6 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [p167]
                    · linarith only [p177]
                    · linarith only [p193]
                    · linarith only [h0, h4, h6, p195n]
                  ·
                    have p167n : -r0 ≤ -(4 / 7 : ℝ) := neg_le_neg (le_of_not_gt p167)
                    by_cases p166 : r2 ≤ (1 / 12 : ℝ)
                    ·
                      refine ⟨12, by decide, ?_⟩
                      change r0 ≤ (7 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 12 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p169]
                      · linarith only [p177]
                      · linarith only [p166]
                      · linarith only [h0, h4, h6, p167n]
                    ·
                      have p166n : -r2 < -(1 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p166)
                      refine ⟨19, by decide, ?_⟩
                      change r0 < (2 / 3 : ℝ) ∧ r1 < (1 / 6 : ℝ) ∧ r2 < (1 / 10 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p169]
                      · linarith only [p177]
                      · linarith only [p193]
                      · linarith only [h0, h6, p167n, p166n]
                ·
                  have p169n : -r0 < -(7 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p169)
                  refine ⟨19, by decide, ?_⟩
                  change r0 < (2 / 3 : ℝ) ∧ r1 < (1 / 6 : ℝ) ∧ r2 < (1 / 10 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [h0, h5, h6, p194n]
                  · linarith only [p177]
                  · linarith only [p193]
                  · linarith only [h0, h6, p194n, p169n]
              ·
                have p177n : -r1 ≤ -(1 / 6 : ℝ) := neg_le_neg (le_of_not_gt p177)
                by_cases p176 : r0 ≤ (5 / 9 : ℝ)
                ·
                  by_cases p174 : r0 < (5 / 9 : ℝ)
                  ·
                    by_cases p172 : r2 ≤ (1 / 12 : ℝ)
                    ·
                      refine ⟨12, by decide, ?_⟩
                      change r0 ≤ (7 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 12 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p176]
                      · linarith only [p181]
                      · linarith only [p172]
                      · linarith only [h0, h4, p195n, p177n]
                    ·
                      have p172n : -r2 < -(1 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p172)
                      refine ⟨31, by decide, ?_⟩
                      change r0 ≤ (11 / 18 : ℝ) ∧ r1 < (1 / 5 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · linarith only [p176]
                      · linarith only [p181]
                      · linarith only [p193]
                      · linarith only [h0, p195n, p177n, p172n]
                  ·
                    have p174n : -r0 ≤ -(5 / 9 : ℝ) := neg_le_neg (le_of_not_gt p174)
                    refine ⟨31, by decide, ?_⟩
                    change r0 ≤ (11 / 18 : ℝ) ∧ r1 < (1 / 5 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [p176]
                    · linarith only [p181]
                    · linarith only [p193]
                    · linarith only [h0, p194n, p177n, p174n]
                ·
                  have p176n : -r0 < -(5 / 9 : ℝ) := neg_lt_neg (lt_of_not_ge p176)
                  refine ⟨31, by decide, ?_⟩
                  change r0 ≤ (11 / 18 : ℝ) ∧ r1 < (1 / 5 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [h0, h5, p194n, p177n]
                  · linarith only [p181]
                  · linarith only [p193]
                  · linarith only [h0, p194n, p177n, p176n]
            ·
              have p181n : -r1 ≤ -(1 / 5 : ℝ) := neg_le_neg (le_of_not_gt p181)
              by_cases p180 : r2 ≤ (1 / 12 : ℝ)
              ·
                refine ⟨12, by decide, ?_⟩
                change r0 ≤ (7 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 ≤ (1 / 12 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [h0, h5, p194n, p181n]
                · linarith only [h0, h5, p195n, p194n]
                · linarith only [p180]
                · linarith only [h0, h4, p195n, p181n]
              ·
                have p180n : -r2 < -(1 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p180)
                refine ⟨32, by decide, ?_⟩
                change r0 ≤ (5 / 9 : ℝ) ∧ r1 ≤ (2 / 9 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [h0, h5, p181n, p180n]
                · linarith only [h0, h5, p195n, p180n]
                · linarith only [p193]
                · linarith only [h0, p195n, p181n, p180n]
          ·
            have p193n : -r2 ≤ -(1 / 10 : ℝ) := neg_le_neg (le_of_not_gt p193)
            by_cases p192 : r2 < (1 / 8 : ℝ)
            ·
              by_cases p190 : r1 < (1 / 6 : ℝ)
              ·
                by_cases p186 : r0 < (4 / 7 : ℝ)
                ·
                  refine ⟨4, by decide, ?_⟩
                  change r0 < (4 / 7 : ℝ) ∧ r1 < (1 / 6 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p186]
                  · linarith only [p190]
                  · linarith only [p192]
                  · linarith only [h0, h6, p195n, p193n]
                ·
                  have p186n : -r0 ≤ -(4 / 7 : ℝ) := neg_le_neg (le_of_not_gt p186)
                  by_cases p185 : r2 < (1 / 9 : ℝ)
                  ·
                    refine ⟨31, by decide, ?_⟩
                    change r0 ≤ (11 / 18 : ℝ) ∧ r1 < (1 / 5 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [h0, h5, h6, p193n]
                    · linarith only [p190]
                    · linarith only [p185]
                    · linarith only [h0, h6, p193n, p186n]
                  ·
                    have p185n : -r2 ≤ -(1 / 9 : ℝ) := neg_le_neg (le_of_not_gt p185)
                    refine ⟨14, by decide, ?_⟩
                    change r0 < (3 / 5 : ℝ) ∧ r1 < (2 / 13 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [h0, h5, h6, p185n]
                    · linarith only [h0, h5, p186n, p185n]
                    · linarith only [p192]
                    · linarith only [h0, h6, p186n, p185n]
              ·
                have p190n : -r1 ≤ -(1 / 6 : ℝ) := neg_le_neg (le_of_not_gt p190)
                by_cases p189 : r2 < (1 / 9 : ℝ)
                ·
                  refine ⟨31, by decide, ?_⟩
                  change r0 ≤ (11 / 18 : ℝ) ∧ r1 < (1 / 5 : ℝ) ∧ r2 < (1 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [h0, h5, p193n, p190n]
                  · linarith only [h0, h5, p195n, p193n]
                  · linarith only [p189]
                  · linarith only [h0, p195n, p193n, p190n]
                ·
                  have p189n : -r2 ≤ -(1 / 9 : ℝ) := neg_le_neg (le_of_not_gt p189)
                  refine ⟨32, by decide, ?_⟩
                  change r0 ≤ (5 / 9 : ℝ) ∧ r1 ≤ (2 / 9 : ℝ) ∧ r2 < (1 / 8 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [h0, h5, p190n, p189n]
                  · linarith only [h0, h5, p195n, p189n]
                  · linarith only [h0, h5, p195n, p190n]
                  · linarith only [h0, p195n, p190n, p189n]
            ·
              have p192n : -r2 ≤ -(1 / 8 : ℝ) := neg_le_neg (le_of_not_gt p192)
              refine ⟨4, by decide, ?_⟩
              change r0 < (4 / 7 : ℝ) ∧ r1 < (1 / 6 : ℝ) ∧ r2 < (1 / 7 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [h0, h5, h6, p192n]
              · linarith only [h0, h5, p195n, p192n]
              · linarith only [h0, h5, h6, p195n]
              · linarith only [h0, h6, p195n, p192n]
  ·
    have p272n : -r2 ≤ -(1 / 7 : ℝ) := neg_le_neg (le_of_not_gt p272)
    by_cases p271 : r1 < (1 / 4 : ℝ)
    ·
      by_cases p235 : r0 ≤ (5 / 12 : ℝ)
      ·
        by_cases p213 : r3 ≤ (1 / 18 : ℝ)
        ·
          refine ⟨11, by decide, ?_⟩
          change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 4 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
          refine ⟨?_, ?_, ?_, ?_⟩
          · linarith only [p235]
          · linarith only [p271]
          · linarith only [h3, p271]
          · linarith only [p213]
        ·
          have p213n : -r3 < -(1 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p213)
          by_cases p212 : r0 ≤ (7 / 18 : ℝ)
          ·
            by_cases p206 : r3 ≤ (1 / 12 : ℝ)
            ·
              refine ⟨11, by decide, ?_⟩
              change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 4 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p212]
              · linarith only [p271]
              · linarith only [h0, h3, h8, p213n]
              · linarith only [p206]
            ·
              have p206n : -r3 < -(1 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p206)
              by_cases p205 : r1 < (2 / 9 : ℝ)
              ·
                by_cases p201 : r3 < (1 / 9 : ℝ)
                ·
                  refine ⟨18, by decide, ?_⟩
                  change r0 ≤ (7 / 18 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 < (1 / 9 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p212]
                  · linarith only [p205]
                  · linarith only [h0, h6, p206n, p205]
                  · linarith only [p201]
                ·
                  have p201n : -r3 ≤ -(1 / 9 : ℝ) := neg_le_neg (le_of_not_gt p201)
                  refine ⟨1, by decide, ?_⟩
                  change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 ≤ (1 / 6 : ℝ) ∧ r3 < (1 / 6 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p212]
                  · linarith only [p205]
                  · linarith only [h0, h6, p205, p201n]
                  · linarith only [h0, h4, h6, h7]
              ·
                have p205n : -r1 ≤ -(2 / 9 : ℝ) := neg_le_neg (le_of_not_gt p205)
                by_cases p204 : r0 < (1 / 3 : ℝ)
                ·
                  refine ⟨3, by decide, ?_⟩
                  change r0 < (1 / 3 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 4 : ℝ) ∧ r3 < (1 / 7 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p204]
                  · linarith only [p271]
                  · linarith only [h0, h3, h8, p206n]
                  · linarith only [h0, h6, h7, p204]
                ·
                  have p204n : -r0 ≤ -(1 / 3 : ℝ) := neg_le_neg (le_of_not_gt p204)
                  refine ⟨18, by decide, ?_⟩
                  change r0 ≤ (7 / 18 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 < (1 / 9 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [h0, p272n, p206n, p205n]
                  · linarith only [p271]
                  · linarith only [h0, h6, p206n, p204n]
                  · linarith only [h0, h7, p205n]
          ·
            have p212n : -r0 < -(7 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p212)
            by_cases p211 : r1 < (2 / 9 : ℝ)
            ·
              by_cases p209 : r3 ≤ (1 / 12 : ℝ)
              ·
                refine ⟨11, by decide, ?_⟩
                change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 4 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [p235]
                · linarith only [p211]
                · linarith only [h0, h3, p213n, p212n]
                · linarith only [p209]
              ·
                have p209n : -r3 < -(1 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p209)
                refine ⟨1, by decide, ?_⟩
                change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 ≤ (1 / 6 : ℝ) ∧ r3 < (1 / 6 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [h0, h6, p272n, p209n]
                · linarith only [h0, p272n, p212n, p209n]
                · linarith only [h0, h6, p212n, p209n]
                · linarith only [h0, h4, h6, p212n]
            ·
              have p211n : -r1 ≤ -(2 / 9 : ℝ) := neg_le_neg (le_of_not_gt p211)
              refine ⟨0, by decide, ?_⟩
              change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [h0, p272n, p213n, p211n]
              · linarith only [p271]
              · linarith only [h0, p213n, p212n, p211n]
              · linarith only [h0, p272n, p212n, p211n]
      ·
        have p235n : -r0 < -(5 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p235)
        by_cases p234 : r1 < (2 / 9 : ℝ)
        ·
          by_cases p230 : r2 < (1 / 6 : ℝ)
          ·
            by_cases p222 : r0 < (4 / 9 : ℝ)
            ·
              refine ⟨20, by decide, ?_⟩
              change r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p222]
              · linarith only [p234]
              · linarith only [p230]
              · linarith only [h0, h6, p272n, p235n]
            ·
              have p222n : -r0 ≤ -(4 / 9 : ℝ) := neg_le_neg (le_of_not_gt p222)
              by_cases p221 : r1 < (3 / 14 : ℝ)
              ·
                by_cases p219 : r3 ≤ (1 / 18 : ℝ)
                ·
                  by_cases p217 : r0 < (1 / 2 : ℝ)
                  ·
                    refine ⟨6, by decide, ?_⟩
                    change r0 < (1 / 2 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [p217]
                    · linarith only [p221]
                    · linarith only [p230]
                    · linarith only [p219]
                  ·
                    have p217n : -r0 ≤ -(1 / 2 : ℝ) := neg_le_neg (le_of_not_gt p217)
                    refine ⟨10, by decide, ?_⟩
                    change r0 < (6 / 11 : ℝ) ∧ r1 < (1 / 5 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [h0, h5, h6, p272n]
                    · linarith only [h0, h5, p272n, p217n]
                    · linarith only [p230]
                    · linarith only [h0, h6, p272n, p217n]
                ·
                  have p219n : -r3 < -(1 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p219)
                  refine ⟨20, by decide, ?_⟩
                  change r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [h0, h6, p272n, p219n]
                  · linarith only [p221]
                  · linarith only [h0, h6, p222n, p219n]
                  · linarith only [h0, h6, p272n, p222n]
              ·
                have p221n : -r1 ≤ -(3 / 14 : ℝ) := neg_le_neg (le_of_not_gt p221)
                refine ⟨6, by decide, ?_⟩
                change r0 < (1 / 2 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [h0, h5, p272n, p221n]
                · linarith only [p234]
                · linarith only [p230]
                · linarith only [h0, p272n, p222n, p221n]
          ·
            have p230n : -r2 ≤ -(1 / 6 : ℝ) := neg_le_neg (le_of_not_gt p230)
            by_cases p229 : r0 < (4 / 9 : ℝ)
            ·
              by_cases p227 : r2 < (1 / 5 : ℝ)
              ·
                refine ⟨6, by decide, ?_⟩
                change r0 < (1 / 2 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [p229]
                · linarith only [p234]
                · linarith only [p227]
                · linarith only [h0, h6, p235n, p230n]
              ·
                have p227n : -r2 ≤ -(1 / 5 : ℝ) := neg_le_neg (le_of_not_gt p227)
                by_cases p226 : r0 < (3 / 7 : ℝ)
                ·
                  refine ⟨23, by decide, ?_⟩
                  change r0 < (3 / 7 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 < (3 / 14 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p226]
                  · linarith only [h0, h5, p235n, p227n]
                  · linarith only [h0, h3, h5, p235n]
                  · linarith only [h0, h6, p235n, p227n]
                ·
                  have p226n : -r0 ≤ -(3 / 7 : ℝ) := neg_le_neg (le_of_not_gt p226)
                  refine ⟨43, by decide, ?_⟩
                  change r0 < (1 / 2 : ℝ) ∧ r1 < (3 / 14 : ℝ) ∧ r2 < (3 / 14 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p229]
                  · linarith only [h0, h5, p227n, p226n]
                  · linarith only [h0, h3, h5, p226n]
                  · linarith only [h0, h6, p227n, p226n]
            ·
              have p229n : -r0 ≤ -(4 / 9 : ℝ) := neg_le_neg (le_of_not_gt p229)
              refine ⟨6, by decide, ?_⟩
              change r0 < (1 / 2 : ℝ) ∧ r1 < (2 / 9 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [h0, h5, h6, p230n]
              · linarith only [p234]
              · linarith only [h0, h3, h5, p229n]
              · linarith only [h0, h6, p230n, p229n]
        ·
          have p234n : -r1 ≤ -(2 / 9 : ℝ) := neg_le_neg (le_of_not_gt p234)
          by_cases p233 : r0 < (4 / 9 : ℝ)
          ·
            refine ⟨37, by decide, ?_⟩
            change r0 < (4 / 9 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
            refine ⟨?_, ?_, ?_, ?_⟩
            · linarith only [p233]
            · linarith only [p271]
            · linarith only [h0, h5, p235n, p234n]
            · linarith only [h0, p272n, p235n, p234n]
          ·
            have p233n : -r0 ≤ -(4 / 9 : ℝ) := neg_le_neg (le_of_not_gt p233)
            refine ⟨20, by decide, ?_⟩
            change r0 < (1 / 2 : ℝ) ∧ r1 < (1 / 4 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
            refine ⟨?_, ?_, ?_, ?_⟩
            · linarith only [h0, h5, p272n, p234n]
            · linarith only [h0, h5, p272n, p233n]
            · linarith only [h0, h5, p234n, p233n]
            · linarith only [h0, p272n, p234n, p233n]
    ·
      have p271n : -r1 ≤ -(1 / 4 : ℝ) := neg_le_neg (le_of_not_gt p271)
      by_cases p270 : r0 ≤ (7 / 18 : ℝ)
      ·
        by_cases p260 : r1 ≤ (5 / 18 : ℝ)
        ·
          by_cases p256 : r0 < (5 / 13 : ℝ)
          ·
            by_cases p252 : r2 < (1 / 5 : ℝ)
            ·
              by_cases p244 : r0 < (3 / 8 : ℝ)
              ·
                by_cases p240 : r2 < (1 / 6 : ℝ)
                ·
                  refine ⟨0, by decide, ?_⟩
                  change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p244]
                  · linarith only [p260]
                  · linarith only [p240]
                  · linarith only [h0, h7, p271n]
                ·
                  have p240n : -r2 ≤ -(1 / 6 : ℝ) := neg_le_neg (le_of_not_gt p240)
                  by_cases p239 : r3 ≤ (1 / 18 : ℝ)
                  ·
                    refine ⟨7, by decide, ?_⟩
                    change r0 < (5 / 13 : ℝ) ∧ r1 < (2 / 7 : ℝ) ∧ r2 < (3 / 14 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [p244]
                    · linarith only [p260]
                    · linarith only [p252]
                    · linarith only [p239]
                  ·
                    have p239n : -r3 < -(1 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p239)
                    refine ⟨45, by decide, ?_⟩
                    change r0 < (4 / 11 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 < (1 / 12 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [h0, p271n, p240n, p239n]
                    · linarith only [h0, h7, p239n]
                    · linarith only [p252]
                    · linarith only [h0, h7, p271n]
              ·
                have p244n : -r0 ≤ -(3 / 8 : ℝ) := neg_le_neg (le_of_not_gt p244)
                by_cases p243 : r2 < (1 / 6 : ℝ)
                ·
                  refine ⟨0, by decide, ?_⟩
                  change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p256]
                  · linarith only [p260]
                  · linarith only [p243]
                  · linarith only [h0, p272n, p271n, p244n]
                ·
                  have p243n : -r2 ≤ -(1 / 6 : ℝ) := neg_le_neg (le_of_not_gt p243)
                  refine ⟨7, by decide, ?_⟩
                  change r0 < (5 / 13 : ℝ) ∧ r1 < (2 / 7 : ℝ) ∧ r2 < (3 / 14 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [p256]
                  · linarith only [p260]
                  · linarith only [p252]
                  · linarith only [h0, p271n, p244n, p243n]
            ·
              have p252n : -r2 ≤ -(1 / 5 : ℝ) := neg_le_neg (le_of_not_gt p252)
              by_cases p251 : r2 < (2 / 9 : ℝ)
              ·
                by_cases p249 : r2 < (3 / 14 : ℝ)
                ·
                  by_cases p247 : r0 < (1 / 3 : ℝ)
                  ·
                    refine ⟨2, by decide, ?_⟩
                    change r0 < (1 / 3 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 4 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [p247]
                    · linarith only [p260]
                    · linarith only [p249]
                    · linarith only [h0, h8, p271n, p252n]
                  ·
                    have p247n : -r0 ≤ -(1 / 3 : ℝ) := neg_le_neg (le_of_not_gt p247)
                    refine ⟨7, by decide, ?_⟩
                    change r0 < (5 / 13 : ℝ) ∧ r1 < (2 / 7 : ℝ) ∧ r2 < (3 / 14 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · linarith only [h0, h5, p271n, p252n]
                    · linarith only [p260]
                    · linarith only [p249]
                    · linarith only [h0, p271n, p252n, p247n]
                ·
                  have p249n : -r2 ≤ -(3 / 14 : ℝ) := neg_le_neg (le_of_not_gt p249)
                  refine ⟨27, by decide, ?_⟩
                  change r0 < (3 / 8 : ℝ) ∧ r1 < (3 / 10 : ℝ) ∧ r2 < (2 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · linarith only [h0, h5, p271n, p249n]
                  · linarith only [p260]
                  · linarith only [p251]
                  · linarith only [h0, h8, p271n, p249n]
              ·
                have p251n : -r2 ≤ -(2 / 9 : ℝ) := neg_le_neg (le_of_not_gt p251)
                refine ⟨39, by decide, ?_⟩
                change r0 < (3 / 8 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 < (1 / 4 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [h0, h5, p271n, p251n]
                · linarith only [p260]
                · linarith only [h0, h5, h8, p271n]
                · linarith only [h0, h8, p271n, p251n]
          ·
            have p256n : -r0 ≤ -(5 / 13 : ℝ) := neg_le_neg (le_of_not_gt p256)
            by_cases p255 : r2 < (1 / 6 : ℝ)
            ·
              refine ⟨0, by decide, ?_⟩
              change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p270]
              · linarith only [p260]
              · linarith only [p255]
              · linarith only [h0, p272n, p271n, p256n]
            ·
              have p255n : -r2 ≤ -(1 / 6 : ℝ) := neg_le_neg (le_of_not_gt p255)
              refine ⟨33, by decide, ?_⟩
              change r0 < (2 / 5 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p270]
              · linarith only [p260]
              · linarith only [h0, h5, p271n, p256n]
              · linarith only [h0, p271n, p256n, p255n]
        ·
          have p260n : -r1 < -(5 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p260)
          by_cases p259 : r2 < (1 / 5 : ℝ)
          ·
            refine ⟨44, by decide, ?_⟩
            change r0 ≤ (7 / 18 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
            refine ⟨?_, ?_, ?_, ?_⟩
            · linarith only [p270]
            · linarith only [h0, h5, h7]
            · linarith only [p259]
            · linarith only [h0, h7, p260n]
          ·
            have p259n : -r2 ≤ -(1 / 5 : ℝ) := neg_le_neg (le_of_not_gt p259)
            refine ⟨27, by decide, ?_⟩
            change r0 < (3 / 8 : ℝ) ∧ r1 < (3 / 10 : ℝ) ∧ r2 < (2 / 9 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
            refine ⟨?_, ?_, ?_, ?_⟩
            · linarith only [h0, h5, p260n, p259n]
            · linarith only [h0, h5, h8, p259n]
            · linarith only [h0, h5, h8, p260n]
            · linarith only [h0, h8, p260n, p259n]
      ·
        have p270n : -r0 < -(7 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p270)
        by_cases p269 : r0 ≤ (5 / 12 : ℝ)
        ·
          by_cases p267 : r1 ≤ (5 / 18 : ℝ)
          ·
            by_cases p265 : r2 < (1 / 6 : ℝ)
            ·
              refine ⟨0, by decide, ?_⟩
              change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
              refine ⟨?_, ?_, ?_, ?_⟩
              · linarith only [p269]
              · linarith only [p267]
              · linarith only [p265]
              · linarith only [h0, p272n, p271n, p270n]
            ·
              have p265n : -r2 ≤ -(1 / 6 : ℝ) := neg_le_neg (le_of_not_gt p265)
              by_cases p264 : r0 < (2 / 5 : ℝ)
              ·
                refine ⟨33, by decide, ?_⟩
                change r0 < (2 / 5 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [p264]
                · linarith only [h0, h5, p270n, p265n]
                · linarith only [h0, h5, p271n, p270n]
                · linarith only [h0, p271n, p270n, p265n]
              ·
                have p264n : -r0 ≤ -(2 / 5 : ℝ) := neg_le_neg (le_of_not_gt p264)
                refine ⟨24, by decide, ?_⟩
                change r0 < (5 / 12 : ℝ) ∧ r1 < (3 / 11 : ℝ) ∧ r2 < (1 / 5 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
                refine ⟨?_, ?_, ?_, ?_⟩
                · linarith only [h0, h5, p271n, p265n]
                · linarith only [h0, h5, p265n, p264n]
                · linarith only [h0, h5, p271n, p264n]
                · linarith only [h0, p271n, p265n, p264n]
          ·
            have p267n : -r1 < -(5 / 18 : ℝ) := neg_lt_neg (lt_of_not_ge p267)
            refine ⟨0, by decide, ?_⟩
            change r0 ≤ (5 / 12 : ℝ) ∧ r1 < (1 / 3 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 12 : ℝ)
            refine ⟨?_, ?_, ?_, ?_⟩
            · linarith only [h0, h5, p272n, p267n]
            · linarith only [h0, h5, p272n, p270n]
            · linarith only [h0, h5, p270n, p267n]
            · linarith only [h0, p272n, p270n, p267n]
        ·
          have p269n : -r0 < -(5 / 12 : ℝ) := neg_lt_neg (lt_of_not_ge p269)
          refine ⟨41, by decide, ?_⟩
          change r0 < (1 / 2 : ℝ) ∧ r1 ≤ (5 / 18 : ℝ) ∧ r2 < (1 / 6 : ℝ) ∧ r3 ≤ (1 / 18 : ℝ)
          refine ⟨?_, ?_, ?_, ?_⟩
          · linarith only [h0, h5, p272n, p271n]
          · linarith only [h0, h5, p272n, p269n]
          · linarith only [h0, h5, p271n, p269n]
          · linarith only [h0, p272n, p271n, p269n]

theorem four_rate_cover (r0 r1 r2 r3 : ℝ)
    (hpos : 0 < r3) (h01 : r1 ≤ r0) (h12 : r2 ≤ r1) (h23 : r3 ≤ r2)
    (hsum : r0 + r1 + r2 + r3 = (5 / 6 : ℝ)) :
    (r0 + 3*r1 ≤ 1 ∨ 2*r0 + 2*r2 ≤ 1 ∨ 3*r0 + r3 ≤ 1) ∨
    (∃ i, i < 47 ∧ Box i r0 r1 r2 r3) := by
  by_cases hA : r0 + 3*r1 ≤ 1
  · exact Or.inl (Or.inl hA)
  by_cases hB : 2*r0 + 2*r2 ≤ 1
  · exact Or.inl (Or.inr (Or.inl hB))
  by_cases hC : 3*r0 + r3 ≤ 1
  · exact Or.inl (Or.inr (Or.inr hC))
  right
  apply finite_cover r0 r1 r2 r3 <;> linarith

#print axioms four_rate_cover
end CertifiedDiscovery.Pinwheel
