import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring.Basic

namespace CertifiedDiscovery.Pinwheel

/-- Finite residue-window checks and a mean-rate bound control every integer window. -/
theorem periodic_window_bound (F : ℤ → ℤ) (P c : ℤ) (r : ℝ)
    (hP : 0 < P)
    (hshift : ∀ t q : ℤ, F (t + q * P) = F t + q * c)
    (hmean : (P : ℝ) * r ≤ c)
    (hsmall : ∀ a b : ℤ, 0 ≤ a → a < P → 0 ≤ b → b < P →
      (b : ℝ) * r < ((F (a + b) - F a : ℤ) : ℝ) + 1)
    (m L : ℤ) (hL : 0 ≤ L) :
    (L : ℝ) * r < ((F (m + L) - F m : ℤ) : ℝ) + 1 := by
  let a := m % P
  let b := L % P
  let q := m / P
  let s := L / P
  have hm : a + q * P = m := Int.emod_add_ediv_mul m P
  have hl : b + s * P = L := Int.emod_add_ediv_mul L P
  have ha0 : 0 ≤ a := Int.emod_nonneg _ (ne_of_gt hP)
  have hb0 : 0 ≤ b := Int.emod_nonneg _ (ne_of_gt hP)
  have haP : a < P := Int.emod_lt_of_pos _ hP
  have hbP : b < P := Int.emod_lt_of_pos _ hP
  have hs0 : 0 ≤ s := Int.ediv_nonneg hL (le_of_lt hP)
  have harg : m + L = a + b + (q + s) * P := by
    calc
      m + L = (a + q * P) + (b + s * P) := by rw [hm, hl]
      _ = a + b + (q + s) * P := by ring1
  have hstart : F m = F a + q * c := by
    calc
      F m = F (a + q * P) := congrArg F hm.symm
      _ = F a + q * c := hshift a q
  have hend : F (m + L) = F (a + b) + (q + s) * c := by
    rw [harg, hshift]
  have hcount : F (m + L) - F m = s * c + (F (a + b) - F a) := by
    rw [hstart, hend]
    ring1
  have hcountR : ((F (m + L) - F m : ℤ) : ℝ) =
      (s : ℝ) * c + ((F (a + b) - F a : ℤ) : ℝ) := by
    exact_mod_cast hcount
  have hlR : (b : ℝ) + (s : ℝ) * P = L := by exact_mod_cast hl
  have hsR : (0 : ℝ) ≤ s := by exact_mod_cast hs0
  have hmul := mul_le_mul_of_nonneg_left hmean hsR
  have hbase := hsmall a b ha0 haP hb0 hbP
  have hlmul := congrArg (fun x : ℝ => x * r) hlR
  nlinarith only [hmul, hbase, hlmul, hcountR]

/-- An integer count with discrepancy strictly below one meets every requested count. -/
theorem window_bound_meets_count (count ell : ℤ) (length rate : ℝ)
    (hbound : length * rate < (count : ℝ) + 1)
    (hrequest : (ell : ℝ) ≤ length * rate) : ell ≤ count := by
  by_contra h
  have hZ : count + 1 ≤ ell := by omega
  have hR : (count : ℝ) + 1 ≤ ell := by exact_mod_cast hZ
  linarith

/-- Cumulative counts of a periodic table, extended to negative times by Euclidean division. -/
def periodicPrefix (P c : ℤ) (pref : ℤ → ℤ) (t : ℤ) : ℤ :=
  (t / P) * c + pref (t % P)

theorem periodicPrefix_shift (P c : ℤ) (hP : P ≠ 0) (pref : ℤ → ℤ)
    (t q : ℤ) :
    periodicPrefix P c pref (t + q * P) = periodicPrefix P c pref t + q * c := by
  simp only [periodicPrefix, Int.add_mul_ediv_right _ _ hP,
    Int.add_mul_emod_self_right]
  ring1

theorem periodic_difference_reduce (F : ℤ → ℤ) (P c : ℤ)
    (hshift : ∀ t q : ℤ, F (t + q * P) = F t + q * c) (m L : ℤ) :
    F (m + L) - F m = F (m % P + L) - F (m % P) := by
  have hm := Int.emod_add_ediv_mul m P
  have harg : m + L = (m % P + L) + (m / P) * P := by omega
  have hstart : F m = F (m % P) + (m / P) * c := by
    calc
      F m = F (m % P + (m / P) * P) := congrArg F hm.symm
      _ = _ := hshift _ _
  rw [harg, hshift, hstart]
  ring1

#print axioms periodic_window_bound
#print axioms periodicPrefix_shift

end CertifiedDiscovery.Pinwheel
