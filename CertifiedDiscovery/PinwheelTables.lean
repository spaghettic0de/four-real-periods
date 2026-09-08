import CertifiedDiscovery.PinwheelTable
import CertifiedDiscovery.PinwheelCover
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CertifiedDiscovery.Pinwheel

def rates (r0 r1 r2 r3 : ℝ) (i : Fin 4) : ℝ :=
  match i.val with | 0 => r0 | 1 => r1 | 2 => r2 | _ => r3

def table0 : PeriodicData where
  period := 12
  counts := fun i => match i.val with
    | 0 => 5
    | 1 => 4
    | 2 => 2
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 1, 2, 2, 3, 3, 4, 4, 4, 5] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨5, 12, true⟩
    | 1 => ⟨1, 3, false⟩
    | 2 => ⟨1, 6, false⟩
    | _ => ⟨1, 12, true⟩
theorem table0_certified : table0.Certified := by decide

theorem table0_bounds (r0 r1 r2 r3 : ℝ) (h : Box 0 r0 r1 r2 r3) :
    table0.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table0, rates] <;> linarith

def table1 : PeriodicData where
  period := 12
  counts := fun i => match i.val with
    | 0 => 5
    | 1 => 3
    | 2 => 2
    | _ => 2
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 3] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨5, 12, true⟩
    | 1 => ⟨2, 9, false⟩
    | 2 => ⟨1, 6, true⟩
    | _ => ⟨1, 6, false⟩
theorem table1_certified : table1.Certified := by decide

theorem table1_bounds (r0 r1 r2 r3 : ℝ) (h : Box 1 r0 r1 r2 r3) :
    table1.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table1, rates] <;> linarith

def table2 : PeriodicData where
  period := 12
  counts := fun i => match i.val with
    | 0 => 4
    | 1 => 4
    | 2 => 3
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 3, 3] : List ℤ).getD t.toNat 0
    | 1 => ([0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 3] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨1, 3, false⟩
    | 1 => ⟨1, 3, false⟩
    | 2 => ⟨1, 4, false⟩
    | _ => ⟨1, 12, true⟩
theorem table2_certified : table2.Certified := by decide

theorem table2_bounds (r0 r1 r2 r3 : ℝ) (h : Box 2 r0 r1 r2 r3) :
    table2.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table2, rates] <;> linarith

def table3 : PeriodicData where
  period := 12
  counts := fun i => match i.val with
    | 0 => 4
    | 1 => 3
    | 2 => 3
    | _ => 2
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨1, 3, false⟩
    | 1 => ⟨1, 4, false⟩
    | 2 => ⟨1, 4, false⟩
    | _ => ⟨1, 7, false⟩
theorem table3_certified : table3.Certified := by decide

theorem table3_bounds (r0 r1 r2 r3 : ℝ) (h : Box 3 r0 r1 r2 r3) :
    table3.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table3, rates] <;> linarith

def table4 : PeriodicData where
  period := 12
  counts := fun i => match i.val with
    | 0 => 7
    | 1 => 2
    | 2 => 2
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 0, 1, 1, 2, 3, 3, 4, 5, 5, 6, 6] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2] : List ℤ).getD t.toNat 0
    | 2 => ([0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨4, 7, false⟩
    | 1 => ⟨1, 6, false⟩
    | 2 => ⟨1, 7, false⟩
    | _ => ⟨1, 12, true⟩
theorem table4_certified : table4.Certified := by decide

theorem table4_bounds (r0 r1 r2 r3 : ℝ) (h : Box 4 r0 r1 r2 r3) :
    table4.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table4, rates] <;> linarith

def table5 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 13
    | 1 => 3
    | 2 => 1
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 3, 4, 4, 5, 6, 6, 7, 8, 8, 9, 10, 10, 11, 12] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨7, 10, false⟩
    | 1 => ⟨1, 6, false⟩
    | 2 => ⟨1, 18, true⟩
    | _ => ⟨1, 18, true⟩
theorem table5_certified : table5.Certified := by decide

theorem table5_bounds (r0 r1 r2 r3 : ℝ) (h : Box 5 r0 r1 r2 r3) :
    table5.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table5, rates] <;> linarith

def table6 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 9
    | 1 => 4
    | 2 => 4
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 2, 2, 3, 3, 3, 4, 4, 5, 6, 6, 7, 7, 7, 8, 9, 9] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨1, 2, false⟩
    | 1 => ⟨2, 9, false⟩
    | 2 => ⟨1, 5, false⟩
    | _ => ⟨1, 18, true⟩
theorem table6_certified : table6.Certified := by decide

theorem table6_bounds (r0 r1 r2 r3 : ℝ) (h : Box 6 r0 r1 r2 r3) :
    table6.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table6, rates] <;> linarith

def table7 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 7
    | 1 => 6
    | 2 => 4
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 1, 2, 2, 2, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨5, 13, false⟩
    | 1 => ⟨2, 7, false⟩
    | 2 => ⟨3, 14, false⟩
    | _ => ⟨1, 18, true⟩
theorem table7_certified : table7.Certified := by decide

theorem table7_bounds (r0 r1 r2 r3 : ℝ) (h : Box 7 r0 r1 r2 r3) :
    table7.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table7, rates] <;> linarith

def table8 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 14
    | 1 => 2
    | 2 => 1
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 3, 4, 4, 5, 6, 7, 7, 8, 9, 10, 10, 11, 12, 13] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨10, 13, false⟩
    | 1 => ⟨1, 9, false⟩
    | 2 => ⟨1, 18, true⟩
    | _ => ⟨1, 18, true⟩
theorem table8_certified : table8.Certified := by decide

theorem table8_bounds (r0 r1 r2 r3 : ℝ) (h : Box 8 r0 r1 r2 r3) :
    table8.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table8, rates] <;> linarith

def table9 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 9
    | 1 => 6
    | 2 => 2
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 1, 2, 2, 3, 3, 4, 5, 5, 6, 6, 6, 7, 7, 8, 8] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 6] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨1, 2, false⟩
    | 1 => ⟨1, 3, false⟩
    | 2 => ⟨1, 9, true⟩
    | _ => ⟨1, 18, true⟩
theorem table9_certified : table9.Certified := by decide

theorem table9_bounds (r0 r1 r2 r3 : ℝ) (h : Box 9 r0 r1 r2 r3) :
    table9.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table9, rates] <;> linarith

def table10 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 10
    | 1 => 4
    | 2 => 3
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨6, 11, false⟩
    | 1 => ⟨1, 5, false⟩
    | 2 => ⟨1, 6, false⟩
    | _ => ⟨1, 18, true⟩
theorem table10_certified : table10.Certified := by decide

theorem table10_bounds (r0 r1 r2 r3 : ℝ) (h : Box 10 r0 r1 r2 r3) :
    table10.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table10, rates] <;> linarith

def table11 : PeriodicData where
  period := 12
  counts := fun i => match i.val with
    | 0 => 5
    | 1 => 3
    | 2 => 3
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨5, 12, true⟩
    | 1 => ⟨1, 4, false⟩
    | 2 => ⟨1, 4, false⟩
    | _ => ⟨1, 12, true⟩
theorem table11_certified : table11.Certified := by decide

theorem table11_bounds (r0 r1 r2 r3 : ℝ) (h : Box 11 r0 r1 r2 r3) :
    table11.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table11, rates] <;> linarith

def table12 : PeriodicData where
  period := 12
  counts := fun i => match i.val with
    | 0 => 7
    | 1 => 3
    | 2 => 1
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 4, 4, 5, 5, 6, 7] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨7, 12, true⟩
    | 1 => ⟨1, 4, false⟩
    | 2 => ⟨1, 12, true⟩
    | _ => ⟨1, 12, true⟩
theorem table12_certified : table12.Certified := by decide

theorem table12_bounds (r0 r1 r2 r3 : ℝ) (h : Box 12 r0 r1 r2 r3) :
    table12.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table12, rates] <;> linarith

def table13 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 8
    | 1 => 6
    | 2 => 3
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 6, 7, 8, 8] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨7, 16, false⟩
    | 1 => ⟨2, 7, false⟩
    | 2 => ⟨2, 13, false⟩
    | _ => ⟨1, 18, true⟩
theorem table13_certified : table13.Certified := by decide

theorem table13_bounds (r0 r1 r2 r3 : ℝ) (h : Box 13 r0 r1 r2 r3) :
    table13.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table13, rates] <;> linarith

def table14 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 11
    | 1 => 3
    | 2 => 3
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 3, 3, 4, 4, 5, 6, 6, 7, 7, 8, 9, 10, 10, 11] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨3, 5, false⟩
    | 1 => ⟨2, 13, false⟩
    | 2 => ⟨1, 7, false⟩
    | _ => ⟨1, 18, true⟩
theorem table14_certified : table14.Certified := by decide

theorem table14_bounds (r0 r1 r2 r3 : ℝ) (h : Box 14 r0 r1 r2 r3) :
    table14.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table14, rates] <;> linarith

def table15 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 10
    | 1 => 5
    | 2 => 2
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨7, 13, false⟩
    | 1 => ⟨1, 4, false⟩
    | 2 => ⟨1, 9, false⟩
    | _ => ⟨1, 18, true⟩
theorem table15_certified : table15.Certified := by decide

theorem table15_bounds (r0 r1 r2 r3 : ℝ) (h : Box 15 r0 r1 r2 r3) :
    table15.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table15, rates] <;> linarith

def table16 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 10
    | 1 => 6
    | 2 => 1
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 6, 6, 7, 7, 8, 8, 9, 9] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 4, 5, 5, 6] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨5, 9, true⟩
    | 1 => ⟨1, 3, false⟩
    | 2 => ⟨1, 18, true⟩
    | _ => ⟨1, 18, true⟩
theorem table16_certified : table16.Certified := by decide

theorem table16_bounds (r0 r1 r2 r3 : ℝ) (h : Box 16 r0 r1 r2 r3) :
    table16.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table16, rates] <;> linarith

def table17 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 8
    | 1 => 5
    | 2 => 3
    | _ => 2
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 1, 2, 2, 3, 3, 4, 4, 4, 5, 5, 6, 6, 7, 7, 8] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 3] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨4, 9, false⟩
    | 1 => ⟨1, 4, false⟩
    | 2 => ⟨1, 8, false⟩
    | _ => ⟨1, 10, false⟩
theorem table17_certified : table17.Certified := by decide

theorem table17_bounds (r0 r1 r2 r3 : ℝ) (h : Box 17 r0 r1 r2 r3) :
    table17.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table17, rates] <;> linarith

def table18 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 7
    | 1 => 5
    | 2 => 4
    | _ => 2
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 7, 7] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 4] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨7, 18, true⟩
    | 1 => ⟨1, 4, false⟩
    | 2 => ⟨1, 5, false⟩
    | _ => ⟨1, 9, false⟩
theorem table18_certified : table18.Certified := by decide

theorem table18_bounds (r0 r1 r2 r3 : ℝ) (h : Box 18 r0 r1 r2 r3) :
    table18.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table18, rates] <;> linarith

def table19 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 12
    | 1 => 3
    | 2 => 2
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 3, 3, 4, 5, 5, 6, 7, 8, 8, 9, 10, 10, 11, 11] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨2, 3, false⟩
    | 1 => ⟨1, 6, false⟩
    | 2 => ⟨1, 10, false⟩
    | _ => ⟨1, 18, true⟩
theorem table19_certified : table19.Certified := by decide

theorem table19_bounds (r0 r1 r2 r3 : ℝ) (h : Box 19 r0 r1 r2 r3) :
    table19.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table19, rates] <;> linarith

def table20 : PeriodicData where
  period := 12
  counts := fun i => match i.val with
    | 0 => 6
    | 1 => 3
    | 2 => 2
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 6] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨1, 2, false⟩
    | 1 => ⟨1, 4, false⟩
    | 2 => ⟨1, 6, false⟩
    | _ => ⟨1, 12, true⟩
theorem table20_certified : table20.Certified := by decide

theorem table20_bounds (r0 r1 r2 r3 : ℝ) (h : Box 20 r0 r1 r2 r3) :
    table20.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table20, rates] <;> linarith

def table21 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 8
    | 1 => 6
    | 2 => 3
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 3, 4, 4, 4, 5, 6, 6, 6, 7, 7, 8, 8] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 6] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨3, 7, false⟩
    | 1 => ⟨3, 10, false⟩
    | 2 => ⟨1, 7, false⟩
    | _ => ⟨1, 18, true⟩
theorem table21_certified : table21.Certified := by decide

theorem table21_bounds (r0 r1 r2 r3 : ℝ) (h : Box 21 r0 r1 r2 r3) :
    table21.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table21, rates] <;> linarith

def table22 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 11
    | 1 => 5
    | 2 => 1
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 4, 4, 5, 6, 6, 7, 7, 8, 9, 9, 10, 10] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨11, 18, true⟩
    | 1 => ⟨1, 4, false⟩
    | 2 => ⟨1, 18, true⟩
    | _ => ⟨1, 18, true⟩
theorem table22_certified : table22.Certified := by decide

theorem table22_bounds (r0 r1 r2 r3 : ℝ) (h : Box 22 r0 r1 r2 r3) :
    table22.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table22, rates] <;> linarith

def table23 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 9
    | 1 => 4
    | 2 => 4
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 2, 2, 3, 3, 4, 4, 5, 6, 6, 7, 7, 7, 8, 8, 9, 9] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨3, 7, false⟩
    | 1 => ⟨2, 9, false⟩
    | 2 => ⟨3, 14, false⟩
    | _ => ⟨1, 18, true⟩
theorem table23_certified : table23.Certified := by decide

theorem table23_bounds (r0 r1 r2 r3 : ℝ) (h : Box 23 r0 r1 r2 r3) :
    table23.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table23, rates] <;> linarith

def table24 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 8
    | 1 => 5
    | 2 => 4
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 7, 7, 7, 8] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨5, 12, false⟩
    | 1 => ⟨3, 11, false⟩
    | 2 => ⟨1, 5, false⟩
    | _ => ⟨1, 18, true⟩
theorem table24_certified : table24.Certified := by decide

theorem table24_bounds (r0 r1 r2 r3 : ℝ) (h : Box 24 r0 r1 r2 r3) :
    table24.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table24, rates] <;> linarith

def table25 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 9
    | 1 => 5
    | 2 => 2
    | _ => 2
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 3, 3, 3, 4, 5, 5, 5, 6, 7, 7, 8, 8, 9, 9] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 4, 5] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨1, 2, false⟩
    | 1 => ⟨5, 18, true⟩
    | 2 => ⟨1, 9, true⟩
    | _ => ⟨1, 9, false⟩
theorem table25_certified : table25.Certified := by decide

theorem table25_bounds (r0 r1 r2 r3 : ℝ) (h : Box 25 r0 r1 r2 r3) :
    table25.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table25, rates] <;> linarith

def table26 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 10
    | 1 => 4
    | 2 => 2
    | _ => 2
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 3, 3, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨7, 13, false⟩
    | 1 => ⟨1, 5, false⟩
    | 2 => ⟨1, 9, false⟩
    | _ => ⟨1, 13, false⟩
theorem table26_certified : table26.Certified := by decide

theorem table26_bounds (r0 r1 r2 r3 : ℝ) (h : Box 26 r0 r1 r2 r3) :
    table26.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table26, rates] <;> linarith

def table27 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 7
    | 1 => 6
    | 2 => 4
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 6, 7, 7] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 4, 5, 5, 6] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨3, 8, false⟩
    | 1 => ⟨3, 10, false⟩
    | 2 => ⟨2, 9, false⟩
    | _ => ⟨1, 18, true⟩
theorem table27_certified : table27.Certified := by decide

theorem table27_bounds (r0 r1 r2 r3 : ℝ) (h : Box 27 r0 r1 r2 r3) :
    table27.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table27, rates] <;> linarith

def table28 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 12
    | 1 => 4
    | 2 => 1
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 4, 5, 5, 6, 6, 7, 8, 8, 9, 10, 11, 11] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨2, 3, false⟩
    | 1 => ⟨2, 9, true⟩
    | 2 => ⟨1, 18, true⟩
    | _ => ⟨1, 18, true⟩
theorem table28_certified : table28.Certified := by decide

theorem table28_bounds (r0 r1 r2 r3 : ℝ) (h : Box 28 r0 r1 r2 r3) :
    table28.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table28, rates] <;> linarith

def table29 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 8
    | 1 => 6
    | 2 => 3
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 6, 7, 7, 8] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨4, 9, false⟩
    | 1 => ⟨2, 7, false⟩
    | 2 => ⟨1, 8, false⟩
    | _ => ⟨1, 18, true⟩
theorem table29_certified : table29.Certified := by decide

theorem table29_bounds (r0 r1 r2 r3 : ℝ) (h : Box 29 r0 r1 r2 r3) :
    table29.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table29, rates] <;> linarith

def table30 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 13
    | 1 => 3
    | 2 => 1
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 2, 2, 3, 4, 5, 5, 6, 7, 7, 8, 9, 10, 10, 11, 12, 12] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨13, 18, true⟩
    | 1 => ⟨1, 7, false⟩
    | 2 => ⟨1, 18, true⟩
    | _ => ⟨1, 18, true⟩
theorem table30_certified : table30.Certified := by decide

theorem table30_bounds (r0 r1 r2 r3 : ℝ) (h : Box 30 r0 r1 r2 r3) :
    table30.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table30, rates] <;> linarith

def table31 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 11
    | 1 => 4
    | 2 => 2
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 3, 3, 4, 4, 5, 6, 6, 7, 7, 8, 9, 9, 10, 11] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3, 3] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨11, 18, true⟩
    | 1 => ⟨1, 5, false⟩
    | 2 => ⟨1, 9, false⟩
    | _ => ⟨1, 18, true⟩
theorem table31_certified : table31.Certified := by decide

theorem table31_bounds (r0 r1 r2 r3 : ℝ) (h : Box 31 r0 r1 r2 r3) :
    table31.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table31, rates] <;> linarith

def table32 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 10
    | 1 => 4
    | 2 => 3
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 6, 6, 7, 7, 8, 8, 9, 9] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨5, 9, true⟩
    | 1 => ⟨2, 9, true⟩
    | 2 => ⟨1, 8, false⟩
    | _ => ⟨1, 18, true⟩
theorem table32_certified : table32.Certified := by decide

theorem table32_bounds (r0 r1 r2 r3 : ℝ) (h : Box 32 r0 r1 r2 r3) :
    table32.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table32, rates] <;> linarith

def table33 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 8
    | 1 => 5
    | 2 => 4
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 8] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨2, 5, false⟩
    | 1 => ⟨5, 18, true⟩
    | 2 => ⟨1, 5, false⟩
    | _ => ⟨1, 18, true⟩
theorem table33_certified : table33.Certified := by decide

theorem table33_bounds (r0 r1 r2 r3 : ℝ) (h : Box 33 r0 r1 r2 r3) :
    table33.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table33, rates] <;> linarith

def table34 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 10
    | 1 => 4
    | 2 => 3
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨7, 13, false⟩
    | 1 => ⟨2, 9, false⟩
    | 2 => ⟨1, 7, false⟩
    | _ => ⟨1, 18, true⟩
theorem table34_certified : table34.Certified := by decide

theorem table34_bounds (r0 r1 r2 r3 : ℝ) (h : Box 34 r0 r1 r2 r3) :
    table34.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table34, rates] <;> linarith

def table35 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 8
    | 1 => 6
    | 2 => 3
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 6, 7, 8, 8] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 6] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨7, 16, false⟩
    | 1 => ⟨1, 3, false⟩
    | 2 => ⟨1, 8, false⟩
    | _ => ⟨1, 18, true⟩
theorem table35_certified : table35.Certified := by decide

theorem table35_bounds (r0 r1 r2 r3 : ℝ) (h : Box 35 r0 r1 r2 r3) :
    table35.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table35, rates] <;> linarith

def table36 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 11
    | 1 => 5
    | 2 => 1
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 4, 4, 5, 6, 7, 7, 8, 8, 9, 9, 10, 11] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨7, 12, false⟩
    | 1 => ⟨5, 18, true⟩
    | 2 => ⟨1, 18, true⟩
    | _ => ⟨1, 18, true⟩
theorem table36_certified : table36.Certified := by decide

theorem table36_bounds (r0 r1 r2 r3 : ℝ) (h : Box 36 r0 r1 r2 r3) :
    table36.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table36, rates] <;> linarith

def table37 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 8
    | 1 => 5
    | 2 => 4
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 5, 6, 6, 7, 7, 8, 8] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨4, 9, false⟩
    | 1 => ⟨1, 4, false⟩
    | 2 => ⟨1, 5, false⟩
    | _ => ⟨1, 18, true⟩
theorem table37_certified : table37.Certified := by decide

theorem table37_bounds (r0 r1 r2 r3 : ℝ) (h : Box 37 r0 r1 r2 r3) :
    table37.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table37, rates] <;> linarith

def table38 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 9
    | 1 => 4
    | 2 => 3
    | _ => 2
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 2, 3, 3, 4, 5, 5, 6, 6, 6, 7, 7, 8, 9] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨1, 2, false⟩
    | 1 => ⟨3, 14, false⟩
    | 2 => ⟨1, 6, false⟩
    | _ => ⟨1, 9, false⟩
theorem table38_certified : table38.Certified := by decide

theorem table38_bounds (r0 r1 r2 r3 : ℝ) (h : Box 38 r0 r1 r2 r3) :
    table38.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table38, rates] <;> linarith

def table39 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 7
    | 1 => 5
    | 2 => 5
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 1, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 4, 5, 5] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨3, 8, false⟩
    | 1 => ⟨5, 18, true⟩
    | 2 => ⟨1, 4, false⟩
    | _ => ⟨1, 18, true⟩
theorem table39_certified : table39.Certified := by decide

theorem table39_bounds (r0 r1 r2 r3 : ℝ) (h : Box 39 r0 r1 r2 r3) :
    table39.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table39, rates] <;> linarith

def table40 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 10
    | 1 => 5
    | 2 => 2
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 10] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨5, 9, false⟩
    | 1 => ⟨5, 18, true⟩
    | 2 => ⟨1, 10, false⟩
    | _ => ⟨1, 18, true⟩
theorem table40_certified : table40.Certified := by decide

theorem table40_bounds (r0 r1 r2 r3 : ℝ) (h : Box 40 r0 r1 r2 r3) :
    table40.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table40, rates] <;> linarith

def table41 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 9
    | 1 => 5
    | 2 => 3
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 1, 2, 2, 3, 4, 4, 4, 5, 6, 6, 7, 7, 8, 8, 9] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 4, 5, 5] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨1, 2, false⟩
    | 1 => ⟨5, 18, true⟩
    | 2 => ⟨1, 6, false⟩
    | _ => ⟨1, 18, true⟩
theorem table41_certified : table41.Certified := by decide

theorem table41_bounds (r0 r1 r2 r3 : ℝ) (h : Box 41 r0 r1 r2 r3) :
    table41.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table41, rates] <;> linarith

def table42 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 10
    | 1 => 4
    | 2 => 2
    | _ => 2
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 7, 8, 9, 9, 10] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨7, 13, false⟩
    | 1 => ⟨2, 11, false⟩
    | 2 => ⟨1, 9, false⟩
    | _ => ⟨1, 10, false⟩
theorem table42_certified : table42.Certified := by decide

theorem table42_bounds (r0 r1 r2 r3 : ℝ) (h : Box 42 r0 r1 r2 r3) :
    table42.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table42, rates] <;> linarith

def table43 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 9
    | 1 => 4
    | 2 => 4
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 2, 2, 3, 3, 3, 4, 4, 5, 6, 6, 7, 7, 7, 8, 8, 9] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨1, 2, false⟩
    | 1 => ⟨3, 14, false⟩
    | 2 => ⟨3, 14, false⟩
    | _ => ⟨1, 18, true⟩
theorem table43_certified : table43.Certified := by decide

theorem table43_bounds (r0 r1 r2 r3 : ℝ) (h : Box 43 r0 r1 r2 r3) :
    table43.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table43, rates] <;> linarith

def table44 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 7
    | 1 => 6
    | 2 => 4
    | _ => 1
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 6, 6, 6, 7] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨7, 18, true⟩
    | 1 => ⟨1, 3, false⟩
    | 2 => ⟨1, 5, false⟩
    | _ => ⟨1, 18, true⟩
theorem table44_certified : table44.Certified := by decide

theorem table44_bounds (r0 r1 r2 r3 : ℝ) (h : Box 44 r0 r1 r2 r3) :
    table44.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table44, rates] <;> linarith

def table45 : PeriodicData where
  period := 18
  counts := fun i => match i.val with
    | 0 => 7
    | 1 => 5
    | 2 => 4
    | _ => 2
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 5, 5, 5, 6, 6, 7, 7] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨4, 11, false⟩
    | 1 => ⟨5, 18, true⟩
    | 2 => ⟨1, 5, false⟩
    | _ => ⟨1, 12, false⟩
theorem table45_certified : table45.Certified := by decide

theorem table45_bounds (r0 r1 r2 r3 : ℝ) (h : Box 45 r0 r1 r2 r3) :
    table45.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table45, rates] <;> linarith

def table46 : PeriodicData where
  period := 12
  counts := fun i => match i.val with
    | 0 => 5
    | 1 => 3
    | 2 => 2
    | _ => 2
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5] : List ℤ).getD t.toNat 0
    | 1 => ([0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := fun i => match i.val with
    | 0 => ⟨5, 12, true⟩
    | 1 => ⟨1, 4, false⟩
    | 2 => ⟨1, 7, false⟩
    | _ => ⟨1, 7, false⟩
theorem table46_certified : table46.Certified := by decide

theorem table46_bounds (r0 r1 r2 r3 : ℝ) (h : Box 46 r0 r1 r2 r3) :
    table46.RateBounds (rates r0 r1 r2 r3) := by
  rcases h with ⟨h0, h1, h2, h3⟩
  intro i
  fin_cases i <;> norm_num [table46, rates] <;> linarith

theorem periodic_box_valid (j : Fin 47) (r0 r1 r2 r3 : ℝ)
    (h : Box j.val r0 r1 r2 r3) :
    ∃ F, CumulativeValid (rates r0 r1 r2 r3) F := by
  fin_cases j
  · exact ⟨table0.eval, table0.valid table0_certified _ (table0_bounds _ _ _ _ h)⟩
  · exact ⟨table1.eval, table1.valid table1_certified _ (table1_bounds _ _ _ _ h)⟩
  · exact ⟨table2.eval, table2.valid table2_certified _ (table2_bounds _ _ _ _ h)⟩
  · exact ⟨table3.eval, table3.valid table3_certified _ (table3_bounds _ _ _ _ h)⟩
  · exact ⟨table4.eval, table4.valid table4_certified _ (table4_bounds _ _ _ _ h)⟩
  · exact ⟨table5.eval, table5.valid table5_certified _ (table5_bounds _ _ _ _ h)⟩
  · exact ⟨table6.eval, table6.valid table6_certified _ (table6_bounds _ _ _ _ h)⟩
  · exact ⟨table7.eval, table7.valid table7_certified _ (table7_bounds _ _ _ _ h)⟩
  · exact ⟨table8.eval, table8.valid table8_certified _ (table8_bounds _ _ _ _ h)⟩
  · exact ⟨table9.eval, table9.valid table9_certified _ (table9_bounds _ _ _ _ h)⟩
  · exact ⟨table10.eval, table10.valid table10_certified _ (table10_bounds _ _ _ _ h)⟩
  · exact ⟨table11.eval, table11.valid table11_certified _ (table11_bounds _ _ _ _ h)⟩
  · exact ⟨table12.eval, table12.valid table12_certified _ (table12_bounds _ _ _ _ h)⟩
  · exact ⟨table13.eval, table13.valid table13_certified _ (table13_bounds _ _ _ _ h)⟩
  · exact ⟨table14.eval, table14.valid table14_certified _ (table14_bounds _ _ _ _ h)⟩
  · exact ⟨table15.eval, table15.valid table15_certified _ (table15_bounds _ _ _ _ h)⟩
  · exact ⟨table16.eval, table16.valid table16_certified _ (table16_bounds _ _ _ _ h)⟩
  · exact ⟨table17.eval, table17.valid table17_certified _ (table17_bounds _ _ _ _ h)⟩
  · exact ⟨table18.eval, table18.valid table18_certified _ (table18_bounds _ _ _ _ h)⟩
  · exact ⟨table19.eval, table19.valid table19_certified _ (table19_bounds _ _ _ _ h)⟩
  · exact ⟨table20.eval, table20.valid table20_certified _ (table20_bounds _ _ _ _ h)⟩
  · exact ⟨table21.eval, table21.valid table21_certified _ (table21_bounds _ _ _ _ h)⟩
  · exact ⟨table22.eval, table22.valid table22_certified _ (table22_bounds _ _ _ _ h)⟩
  · exact ⟨table23.eval, table23.valid table23_certified _ (table23_bounds _ _ _ _ h)⟩
  · exact ⟨table24.eval, table24.valid table24_certified _ (table24_bounds _ _ _ _ h)⟩
  · exact ⟨table25.eval, table25.valid table25_certified _ (table25_bounds _ _ _ _ h)⟩
  · exact ⟨table26.eval, table26.valid table26_certified _ (table26_bounds _ _ _ _ h)⟩
  · exact ⟨table27.eval, table27.valid table27_certified _ (table27_bounds _ _ _ _ h)⟩
  · exact ⟨table28.eval, table28.valid table28_certified _ (table28_bounds _ _ _ _ h)⟩
  · exact ⟨table29.eval, table29.valid table29_certified _ (table29_bounds _ _ _ _ h)⟩
  · exact ⟨table30.eval, table30.valid table30_certified _ (table30_bounds _ _ _ _ h)⟩
  · exact ⟨table31.eval, table31.valid table31_certified _ (table31_bounds _ _ _ _ h)⟩
  · exact ⟨table32.eval, table32.valid table32_certified _ (table32_bounds _ _ _ _ h)⟩
  · exact ⟨table33.eval, table33.valid table33_certified _ (table33_bounds _ _ _ _ h)⟩
  · exact ⟨table34.eval, table34.valid table34_certified _ (table34_bounds _ _ _ _ h)⟩
  · exact ⟨table35.eval, table35.valid table35_certified _ (table35_bounds _ _ _ _ h)⟩
  · exact ⟨table36.eval, table36.valid table36_certified _ (table36_bounds _ _ _ _ h)⟩
  · exact ⟨table37.eval, table37.valid table37_certified _ (table37_bounds _ _ _ _ h)⟩
  · exact ⟨table38.eval, table38.valid table38_certified _ (table38_bounds _ _ _ _ h)⟩
  · exact ⟨table39.eval, table39.valid table39_certified _ (table39_bounds _ _ _ _ h)⟩
  · exact ⟨table40.eval, table40.valid table40_certified _ (table40_bounds _ _ _ _ h)⟩
  · exact ⟨table41.eval, table41.valid table41_certified _ (table41_bounds _ _ _ _ h)⟩
  · exact ⟨table42.eval, table42.valid table42_certified _ (table42_bounds _ _ _ _ h)⟩
  · exact ⟨table43.eval, table43.valid table43_certified _ (table43_bounds _ _ _ _ h)⟩
  · exact ⟨table44.eval, table44.valid table44_certified _ (table44_bounds _ _ _ _ h)⟩
  · exact ⟨table45.eval, table45.valid table45_certified _ (table45_bounds _ _ _ _ h)⟩
  · exact ⟨table46.eval, table46.valid table46_certified _ (table46_bounds _ _ _ _ h)⟩

#print axioms periodic_box_valid
end CertifiedDiscovery.Pinwheel
