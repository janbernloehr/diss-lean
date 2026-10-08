import NLS.ZakharovShabat.SourceBirkhoffM1Coordinates

/-! # Exact physical Sobolev coordinates at every real order -/
noncomputable section
namespace NLS.ZakharovShabat

/-- The original physical source represented by normalized H^s coordinates. -/
def sourceRealSobolevInclusion (r : ℝ) (hr : 0 ≤ r) (a : CoeffPair 2) : CoeffPair 2 :=
  normalizedWeightedSource (SpectralWeight.piSobolev r hr) a

@[simp] theorem sourceRealSobolevInclusion_fst (r : ℝ) (hr : 0 ≤ r) (a : CoeffPair 2) (n : ℤ) :
    (sourceRealSobolevInclusion r hr a).fst n =
      a.fst n / (((1+|((2*n:ℤ):ℝ)*Real.pi|)^r : ℝ) : ℂ) := by
  simp only [sourceRealSobolevInclusion,normalizedWeightedSource_fst,SpectralWeight.piSobolev_apply]

@[simp] theorem sourceRealSobolevInclusion_snd (r : ℝ) (hr : 0 ≤ r) (a : CoeffPair 2) (n : ℤ) :
    (sourceRealSobolevInclusion r hr a).snd n =
      a.snd n / (((1+|((2*n:ℤ):ℝ)*Real.pi|)^r : ℝ) : ℂ) := by
  simp only [sourceRealSobolevInclusion,normalizedWeightedSource_snd,SpectralWeight.piSobolev_apply]

/-- The literal ℓ^{2s,1} summand of the actual action sequence, at a real order. -/
def sourceRealSobolevActionTerm (r : ℝ) (hr : 0 ≤ r) (a : CoeffPair 2) (n : ℤ) : ℝ :=
  (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*r)*
    ‖sourceComplexAction (by simp) (by norm_num) n (sourceRealSobolevInclusion r hr a)‖

/-- Squared Sobolev weights give the exact real exponent 2s in the action norm. -/
theorem sourceRealSobolevActionTerm_eq (r : ℝ) (hr : 0 ≤ r) (a : CoeffPair 2) (n : ℤ) :
    sourceRealSobolevActionTerm r hr a n =
      sourceM1ActionTerm (SpectralWeight.piSobolev r hr)
        (normalizedWeightedSource (SpectralWeight.piSobolev r hr) a) n := by
  unfold sourceRealSobolevActionTerm sourceRealSobolevInclusion sourceM1ActionTerm
  rw [SpectralWeight.piSobolev_apply,← Real.rpow_mul_natCast (by positivity),Nat.cast_ofNat,mul_comm r 2]

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)}
  {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The actual weighted Birkhoff image in the real Hilbert model of h^s. -/
def realSobolevCoordinates
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (r : ℝ) (hr : 1 ≤ r) (a : realTypeSourceSubmodule 2) : WithLp 2 (RealCoeff 2 × RealCoeff 2) :=
  D.m1Coordinates (SpectralWeight.piSobolev r (zero_le_one.trans hr))
    (SpectralWeight.hasLinearFactor_piSobolev r hr) a

@[simp] theorem realSobolevCoordinates_fst
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (r : ℝ) (hr : 1 ≤ r) (a : realTypeSourceSubmodule 2) (n : ℤ) :
    (D.realSobolevCoordinates r hr a).fst n = (1+|((2*n:ℤ):ℝ)*Real.pi|)^r*
      (sourceRealBirkhoffMap (by simp) (by norm_num) s
        (normalizedWeightedRealSource (SpectralWeight.piSobolev r (zero_le_one.trans hr)) a)).1 n := by
  simp only [realSobolevCoordinates,m1Coordinates_fst,SpectralWeight.piSobolev_apply]

@[simp] theorem realSobolevCoordinates_snd
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (r : ℝ) (hr : 1 ≤ r) (a : realTypeSourceSubmodule 2) (n : ℤ) :
    (D.realSobolevCoordinates r hr a).snd n = (1+|((2*n:ℤ):ℝ)*Real.pi|)^r*
      (sourceRealBirkhoffMap (by simp) (by norm_num) s
        (normalizedWeightedRealSource (SpectralWeight.piSobolev r (zero_le_one.trans hr)) a)).2 n := by
  simp only [realSobolevCoordinates,m1Coordinates_snd,SpectralWeight.piSobolev_apply]

/-- Exact weighted Parseval identity at a real Sobolev order. -/
theorem realSobolevCoordinates_norm_sq
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (r : ℝ) (hr : 1 ≤ r) (a : realTypeSourceSubmodule 2) :
    ‖D.realSobolevCoordinates r hr a‖^2 =
      2*(∑' n : ℤ, sourceRealSobolevActionTerm r (zero_le_one.trans hr) a.val n) := by
  simp only [realSobolevCoordinates,m1Coordinates_norm_sq,sourceRealSobolevActionTerm_eq]

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
