import CertifiedDiscovery.PinwheelPeriods
open CertifiedDiscovery.Pinwheel

-- Expected compilation failure: intentionally invalid certificate.
def closedCapTable0 : PeriodicData where
  period := table0.period
  counts := table0.counts
  pref := table0.pref
  caps := fun i => match i.val with
    | 0 => ⟨5, 12, true⟩
    | 1 => ⟨1, 3, true⟩
    | 2 => ⟨1, 6, false⟩
    | _ => ⟨1, 12, true⟩
example : closedCapTable0.Certified := by decide
