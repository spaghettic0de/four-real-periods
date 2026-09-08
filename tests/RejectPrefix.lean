import CertifiedDiscovery.PinwheelPeriods
open CertifiedDiscovery.Pinwheel

-- Expected compilation failure: intentionally invalid certificate.
def badTable0 : PeriodicData where
  period := 12
  counts := table0.counts
  pref := fun i t => match i.val with
    | 0 => ([0, 1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5] : List ℤ).getD t.toNat 0   -- changed slot 10: 4 -> 5
    | 1 => ([0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3] : List ℤ).getD t.toNat 0
    | 2 => ([0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2] : List ℤ).getD t.toNat 0
    | _ => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1] : List ℤ).getD t.toNat 0
  caps := table0.caps
example : badTable0.Certified := by decide
