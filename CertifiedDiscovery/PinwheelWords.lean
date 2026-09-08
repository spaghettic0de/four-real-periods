set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertifiedDiscovery.Pinwheel

structure RateCap where
  num : Nat
  den : Nat
  closed : Bool
  deriving Repr, DecidableEq

def windowCount (w : List Nat) (i m len : Nat) : Nat :=
  ((List.range len).filter fun t => w[(m + t) % w.length]? == some i).length

def taskChecked (w : List Nat) (i : Nat) (c : RateCap) : Bool :=
  c.num > 0 && c.den > 0 &&
  c.num * w.length ≤ c.den * windowCount w i 0 w.length &&
  (List.range w.length).all (fun m =>
    (List.range w.length).all (fun len =>
      if c.closed then c.num * len < c.den * (windowCount w i m len + 1)
      else c.num * len ≤ c.den * (windowCount w i m len + 1)))

def wordChecked (w : List Nat) (caps : List RateCap) : Bool :=
  w.length > 0 && caps.length == 4 && (w.all fun i => i < 4) &&
  ((List.range 4).all fun i => match caps[i]? with
    | some c => taskChecked w i c
    | none => false)

def word0 : List Nat := [0, 2, 1, 0, 3, 0, 1, 0, 2, 1, 0, 1]
def caps0 : List RateCap := [⟨5, 12, true⟩, ⟨1, 3, false⟩, ⟨1, 6, false⟩, ⟨1, 12, true⟩]
theorem word0_checked : wordChecked word0 caps0 = true := by decide

def word1 : List Nat := [0, 3, 0, 1, 0, 2, 3, 0, 1, 0, 1, 2]
def caps1 : List RateCap := [⟨5, 12, true⟩, ⟨2, 9, false⟩, ⟨1, 6, true⟩, ⟨1, 6, false⟩]
theorem word1_checked : wordChecked word1 caps1 = true := by decide

def word2 : List Nat := [1, 3, 2, 0, 1, 2, 0, 1, 0, 1, 2, 0]
def caps2 : List RateCap := [⟨1, 3, false⟩, ⟨1, 3, false⟩, ⟨1, 4, false⟩, ⟨1, 12, true⟩]
theorem word2_checked : wordChecked word2 caps2 = true := by decide

def word3 : List Nat := [0, 2, 3, 0, 1, 2, 3, 0, 1, 0, 2, 1]
def caps3 : List RateCap := [⟨1, 3, false⟩, ⟨1, 4, false⟩, ⟨1, 4, false⟩, ⟨1, 7, false⟩]
theorem word3_checked : wordChecked word3 caps3 = true := by decide

def word4 : List Nat := [2, 0, 3, 0, 0, 1, 0, 0, 2, 0, 1, 0]
def caps4 : List RateCap := [⟨4, 7, false⟩, ⟨1, 6, false⟩, ⟨1, 7, false⟩, ⟨1, 12, true⟩]
theorem word4_checked : wordChecked word4 caps4 = true := by decide

def word5 : List Nat := [0, 1, 0, 0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0]
def caps5 : List RateCap := [⟨7, 10, false⟩, ⟨1, 6, false⟩, ⟨1, 18, true⟩, ⟨1, 18, true⟩]
theorem word5_checked : wordChecked word5 caps5 = true := by decide

def word6 : List Nat := [0, 0, 1, 0, 2, 3, 0, 1, 0, 0, 2, 0, 1, 2, 0, 0, 1, 2]
def caps6 : List RateCap := [⟨1, 2, false⟩, ⟨2, 9, false⟩, ⟨1, 5, false⟩, ⟨1, 18, true⟩]
theorem word6_checked : wordChecked word6 caps6 = true := by decide

def word7 : List Nat := [0, 1, 2, 0, 3, 1, 0, 2, 0, 1, 0, 1, 2, 0, 1, 2, 0, 1]
def caps7 : List RateCap := [⟨5, 13, false⟩, ⟨2, 7, false⟩, ⟨3, 14, false⟩, ⟨1, 18, true⟩]
theorem word7_checked : wordChecked word7 caps7 = true := by decide

def word8 : List Nat := [0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0]
def caps8 : List RateCap := [⟨10, 13, false⟩, ⟨1, 9, false⟩, ⟨1, 18, true⟩, ⟨1, 18, true⟩]
theorem word8_checked : wordChecked word8 caps8 = true := by decide

def word9 : List Nat := [0, 1, 2, 0, 1, 0, 1, 0, 0, 1, 0, 2, 1, 0, 3, 0, 1, 0]
def caps9 : List RateCap := [⟨1, 2, false⟩, ⟨1, 3, false⟩, ⟨1, 9, true⟩, ⟨1, 18, true⟩]
theorem word9_checked : wordChecked word9 caps9 = true := by decide

def word10 : List Nat := [0, 1, 0, 2, 0, 0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 1, 0]
def caps10 : List RateCap := [⟨6, 11, false⟩, ⟨1, 5, false⟩, ⟨1, 6, false⟩, ⟨1, 18, true⟩]
theorem word10_checked : wordChecked word10 caps10 = true := by decide

def word11 : List Nat := [0, 1, 0, 2, 1, 0, 2, 0, 3, 1, 0, 2]
def caps11 : List RateCap := [⟨5, 12, true⟩, ⟨1, 4, false⟩, ⟨1, 4, false⟩, ⟨1, 12, true⟩]
theorem word11_checked : wordChecked word11 caps11 = true := by decide

def word12 : List Nat := [0, 2, 0, 1, 0, 0, 3, 0, 1, 0, 0, 1]
def caps12 : List RateCap := [⟨7, 12, true⟩, ⟨1, 4, false⟩, ⟨1, 12, true⟩, ⟨1, 12, true⟩]
theorem word12_checked : wordChecked word12 caps12 = true := by decide

def word13 : List Nat := [0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 3, 0, 1, 2, 0, 0, 1, 2]
def caps13 : List RateCap := [⟨7, 16, false⟩, ⟨2, 7, false⟩, ⟨2, 13, false⟩, ⟨1, 18, true⟩]
theorem word13_checked : wordChecked word13 caps13 = true := by decide

def word14 : List Nat := [0, 3, 0, 0, 1, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 2]
def caps14 : List RateCap := [⟨3, 5, false⟩, ⟨2, 13, false⟩, ⟨1, 7, false⟩, ⟨1, 18, true⟩]
theorem word14_checked : wordChecked word14 caps14 = true := by decide

def word15 : List Nat := [0, 1, 0, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]
def caps15 : List RateCap := [⟨7, 13, false⟩, ⟨1, 4, false⟩, ⟨1, 9, false⟩, ⟨1, 18, true⟩]
theorem word15_checked : wordChecked word15 caps15 = true := by decide

def word16 : List Nat := [0, 1, 0, 2, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 1, 0, 1, 0]
def caps16 : List RateCap := [⟨5, 9, true⟩, ⟨1, 3, false⟩, ⟨1, 18, true⟩, ⟨1, 18, true⟩]
theorem word16_checked : wordChecked word16 caps16 = true := by decide

def word17 : List Nat := [0, 1, 2, 0, 1, 0, 3, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 3]
def caps17 : List RateCap := [⟨4, 9, false⟩, ⟨1, 4, false⟩, ⟨1, 8, false⟩, ⟨1, 10, false⟩]
theorem word17_checked : wordChecked word17 caps17 = true := by decide

def word18 : List Nat := [0, 1, 0, 3, 2, 0, 1, 0, 1, 2, 0, 3, 1, 0, 2, 0, 2, 1]
def caps18 : List RateCap := [⟨7, 18, true⟩, ⟨1, 4, false⟩, ⟨1, 5, false⟩, ⟨1, 9, false⟩]
theorem word18_checked : wordChecked word18 caps18 = true := by decide

def word19 : List Nat := [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0]
def caps19 : List RateCap := [⟨2, 3, false⟩, ⟨1, 6, false⟩, ⟨1, 10, false⟩, ⟨1, 18, true⟩]
theorem word19_checked : wordChecked word19 caps19 = true := by decide

def word20 : List Nat := [0, 2, 0, 1, 0, 3, 2, 0, 1, 0, 0, 1]
def caps20 : List RateCap := [⟨1, 2, false⟩, ⟨1, 4, false⟩, ⟨1, 6, false⟩, ⟨1, 12, true⟩]
theorem word20_checked : wordChecked word20 caps20 = true := by decide

def word21 : List Nat := [0, 1, 0, 2, 0, 1, 0, 3, 1, 0, 0, 2, 1, 0, 1, 0, 1, 2]
def caps21 : List RateCap := [⟨3, 7, false⟩, ⟨3, 10, false⟩, ⟨1, 7, false⟩, ⟨1, 18, true⟩]
theorem word21_checked : wordChecked word21 caps21 = true := by decide

def word22 : List Nat := [0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0, 1, 0, 0, 1, 0, 2, 0]
def caps22 : List RateCap := [⟨11, 18, true⟩, ⟨1, 4, false⟩, ⟨1, 18, true⟩, ⟨1, 18, true⟩]
theorem word22_checked : wordChecked word22 caps22 = true := by decide

def word23 : List Nat := [0, 0, 1, 0, 2, 0, 1, 0, 0, 2, 0, 1, 2, 0, 3, 0, 1, 2]
def caps23 : List RateCap := [⟨3, 7, false⟩, ⟨2, 9, false⟩, ⟨3, 14, false⟩, ⟨1, 18, true⟩]
theorem word23_checked : wordChecked word23 caps23 = true := by decide

def word24 : List Nat := [0, 1, 0, 0, 2, 1, 0, 3, 0, 1, 2, 0, 1, 0, 2, 1, 0, 2]
def caps24 : List RateCap := [⟨5, 12, false⟩, ⟨3, 11, false⟩, ⟨1, 5, false⟩, ⟨1, 18, true⟩]
theorem word24_checked : wordChecked word24 caps24 = true := by decide

def word25 : List Nat := [0, 1, 0, 0, 3, 1, 0, 0, 2, 1, 0, 0, 1, 0, 3, 0, 1, 2]
def caps25 : List RateCap := [⟨1, 2, false⟩, ⟨5, 18, true⟩, ⟨1, 9, true⟩, ⟨1, 9, false⟩]
theorem word25_checked : wordChecked word25 caps25 = true := by decide

def word26 : List Nat := [0, 1, 0, 0, 1, 0, 0, 2, 0, 1, 0, 3, 0, 1, 0, 3, 0, 2]
def caps26 : List RateCap := [⟨7, 13, false⟩, ⟨1, 5, false⟩, ⟨1, 9, false⟩, ⟨1, 13, false⟩]
theorem word26_checked : wordChecked word26 caps26 = true := by decide

def word27 : List Nat := [0, 1, 0, 1, 2, 0, 3, 1, 0, 2, 1, 0, 0, 2, 1, 0, 1, 2]
def caps27 : List RateCap := [⟨3, 8, false⟩, ⟨3, 10, false⟩, ⟨2, 9, false⟩, ⟨1, 18, true⟩]
theorem word27_checked : wordChecked word27 caps27 = true := by decide

def word28 : List Nat := [0, 2, 0, 1, 0, 0, 0, 1, 0, 3, 0, 0, 1, 0, 0, 0, 1, 0]
def caps28 : List RateCap := [⟨2, 3, false⟩, ⟨2, 9, true⟩, ⟨1, 18, true⟩, ⟨1, 18, true⟩]
theorem word28_checked : wordChecked word28 caps28 = true := by decide

def word29 : List Nat := [0, 3, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 2, 0, 1, 0, 1]
def caps29 : List RateCap := [⟨4, 9, false⟩, ⟨2, 7, false⟩, ⟨1, 8, false⟩, ⟨1, 18, true⟩]
theorem word29_checked : wordChecked word29 caps29 = true := by decide

def word30 : List Nat := [0, 0, 2, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 3, 0, 0, 1, 0]
def caps30 : List RateCap := [⟨13, 18, true⟩, ⟨1, 7, false⟩, ⟨1, 18, true⟩, ⟨1, 18, true⟩]
theorem word30_checked : wordChecked word30 caps30 = true := by decide

def word31 : List Nat := [0, 3, 0, 0, 1, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 1]
def caps31 : List RateCap := [⟨11, 18, true⟩, ⟨1, 5, false⟩, ⟨1, 9, false⟩, ⟨1, 18, true⟩]
theorem word31_checked : wordChecked word31 caps31 = true := by decide

def word32 : List Nat := [0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 3, 0, 1, 0]
def caps32 : List RateCap := [⟨5, 9, true⟩, ⟨2, 9, true⟩, ⟨1, 8, false⟩, ⟨1, 18, true⟩]
theorem word32_checked : wordChecked word32 caps32 = true := by decide

def word33 : List Nat := [0, 2, 0, 1, 0, 2, 1, 0, 2, 0, 1, 3, 0, 2, 1, 0, 0, 1]
def caps33 : List RateCap := [⟨2, 5, false⟩, ⟨5, 18, true⟩, ⟨1, 5, false⟩, ⟨1, 18, true⟩]
theorem word33_checked : wordChecked word33 caps33 = true := by decide

def word34 : List Nat := [0, 1, 0, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 2, 0]
def caps34 : List RateCap := [⟨7, 13, false⟩, ⟨2, 9, false⟩, ⟨1, 7, false⟩, ⟨1, 18, true⟩]
theorem word34_checked : wordChecked word34 caps34 = true := by decide

def word35 : List Nat := [0, 1, 0, 1, 0, 3, 1, 0, 2, 0, 1, 0, 1, 2, 0, 0, 1, 2]
def caps35 : List RateCap := [⟨7, 16, false⟩, ⟨1, 3, false⟩, ⟨1, 8, false⟩, ⟨1, 18, true⟩]
theorem word35_checked : wordChecked word35 caps35 = true := by decide

def word36 : List Nat := [0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 3, 0, 1, 0, 0, 1]
def caps36 : List RateCap := [⟨7, 12, false⟩, ⟨5, 18, true⟩, ⟨1, 18, true⟩, ⟨1, 18, true⟩]
theorem word36_checked : wordChecked word36 caps36 = true := by decide

def word37 : List Nat := [0, 1, 0, 1, 0, 2, 0, 1, 0, 3, 2, 0, 1, 0, 2, 0, 1, 2]
def caps37 : List RateCap := [⟨4, 9, false⟩, ⟨1, 4, false⟩, ⟨1, 5, false⟩, ⟨1, 18, true⟩]
theorem word37_checked : wordChecked word37 caps37 = true := by decide

def word38 : List Nat := [0, 1, 0, 3, 1, 0, 2, 0, 0, 1, 0, 3, 2, 0, 1, 0, 0, 2]
def caps38 : List RateCap := [⟨1, 2, false⟩, ⟨3, 14, false⟩, ⟨1, 6, false⟩, ⟨1, 9, false⟩]
theorem word38_checked : wordChecked word38 caps38 = true := by decide

def word39 : List Nat := [0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 1, 3, 0, 2, 1, 0, 2]
def caps39 : List RateCap := [⟨3, 8, false⟩, ⟨5, 18, true⟩, ⟨1, 4, false⟩, ⟨1, 18, true⟩]
theorem word39_checked : wordChecked word39 caps39 = true := by decide

def word40 : List Nat := [0, 2, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 0, 1]
def caps40 : List RateCap := [⟨5, 9, false⟩, ⟨5, 18, true⟩, ⟨1, 10, false⟩, ⟨1, 18, true⟩]
theorem word40_checked : wordChecked word40 caps40 = true := by decide

def word41 : List Nat := [0, 1, 2, 0, 1, 0, 0, 2, 1, 0, 0, 1, 0, 2, 0, 1, 0, 3]
def caps41 : List RateCap := [⟨1, 2, false⟩, ⟨5, 18, true⟩, ⟨1, 6, false⟩, ⟨1, 18, true⟩]
theorem word41_checked : wordChecked word41 caps41 = true := by decide

def word42 : List Nat := [0, 1, 0, 1, 0, 3, 0, 2, 0, 1, 0, 0, 3, 0, 0, 1, 0, 2]
def caps42 : List RateCap := [⟨7, 13, false⟩, ⟨2, 11, false⟩, ⟨1, 9, false⟩, ⟨1, 10, false⟩]
theorem word42_checked : wordChecked word42 caps42 = true := by decide

def word43 : List Nat := [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 1, 0, 2, 3, 0, 1, 0, 2]
def caps43 : List RateCap := [⟨1, 2, false⟩, ⟨3, 14, false⟩, ⟨3, 14, false⟩, ⟨1, 18, true⟩]
theorem word43_checked : wordChecked word43 caps43 = true := by decide

def word44 : List Nat := [0, 1, 2, 0, 1, 0, 2, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 3]
def caps44 : List RateCap := [⟨7, 18, true⟩, ⟨1, 3, false⟩, ⟨1, 5, false⟩, ⟨1, 18, true⟩]
theorem word44_checked : wordChecked word44 caps44 = true := by decide

def word45 : List Nat := [0, 1, 2, 0, 3, 1, 0, 2, 1, 0, 0, 2, 1, 0, 2, 0, 1, 3]
def caps45 : List RateCap := [⟨4, 11, false⟩, ⟨5, 18, true⟩, ⟨1, 5, false⟩, ⟨1, 12, false⟩]
theorem word45_checked : wordChecked word45 caps45 = true := by decide

def word46 : List Nat := [0, 1, 0, 3, 2, 0, 1, 0, 2, 1, 0, 3]
def caps46 : List RateCap := [⟨5, 12, true⟩, ⟨1, 4, false⟩, ⟨1, 7, false⟩, ⟨1, 7, false⟩]
theorem word46_checked : wordChecked word46 caps46 = true := by decide

#print axioms word0_checked
#print axioms word46_checked
end CertifiedDiscovery.Pinwheel
