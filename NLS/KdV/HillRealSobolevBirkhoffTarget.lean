import NLS.KdV.HillOriginalBirkhoffWeightedRestriction
import NLS.SequenceSpaces.RealWeightedNatPairInclusion
import NLS.SequenceSpaces.SobolevCorollaryWeights

noncomputable section
set_option autoImplicit false
namespace NLS.KdV

/-- Exact homogeneous normalization for every real Sobolev exponent. -/
def hillBirkhoffRealSobolevWeight (s : ℝ) (k : ℕ) : ℝ :=
  (2*Real.pi*(k+1 : ℕ))^s*hillBirkhoffBaseWeight k

theorem hillBirkhoffRealSobolevWeight_pos (s : ℝ) (k : ℕ) :
    0 < hillBirkhoffRealSobolevWeight s k := by
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) s) (hillBirkhoffBaseWeight_pos k)

abbrev HillBirkhoffRealSobolevSpace (s : ℝ) := RealWeightedNatPair
  (hillBirkhoffRealSobolevWeight s) (hillBirkhoffRealSobolevWeight_pos s)

theorem hillBirkhoffRealSobolevWeight_sq (s : ℝ) (k : ℕ) :
    (hillBirkhoffRealSobolevWeight s k)^2 = (2*Real.pi*(k+1 : ℕ))^(2*s+1) := by
  rw [hillBirkhoffRealSobolevWeight,mul_pow,hillBirkhoffBaseWeight,
    Real.sq_sqrt (by positivity),← Real.rpow_mul_natCast (by positivity)]
  rw [← Real.rpow_add_one (by positivity : (2*Real.pi*(k+1 : ℕ)) ≠ 0)]
  congr 1
  norm_num
  ring

theorem summable_HillBirkhoffRealSobolevSpace_sq (s : ℝ) (z : HillBirkhoffRealSobolevSpace s) :
    Summable (fun k : ℕ => (2*Real.pi*(k+1 : ℕ))^(2*s+1)*
      ((z.val k).1^2+(z.val k).2^2)) := by
  simpa only [hillBirkhoffRealSobolevWeight_sq] using
    RealWeightedNatPair.summable_weighted_sq _ _ z

theorem norm_HillBirkhoffRealSobolevSpace_sq (s : ℝ) (z : HillBirkhoffRealSobolevSpace s) :
    ‖z‖^2 = ∑' k : ℕ, (2*Real.pi*(k+1 : ℕ))^(2*s+1)*
      ((z.val k).1^2+(z.val k).2^2) := by
  simpa only [hillBirkhoffRealSobolevWeight_sq] using
    RealWeightedNatPair.norm_sq_eq_tsum _ _ z

/-- Preserve all raw pairs while passing from the inhomogeneous split weight
to the exact homogeneous real-exponent target. -/
def hillCorollaryTarget (s : ℝ) (hs : 0 ≤ s)
    (z : HillBirkhoffWeightedSpace (SpectralWeight.corollaryWeight s hs)) :
    HillBirkhoffRealSobolevSpace s :=
  RealWeightedNatPair.inclusion _ _ _ _ (Real.pi^(SpectralWeight.corollarySplit s)) (by positivity)
    (fun k => by
      dsimp only [hillBirkhoffRealSobolevWeight,hillBirkhoffWeightedWeight]
      exact (mul_le_mul_of_nonneg_right (SpectralWeight.corollaryWeight_homogeneous s hs (k+1))
        (hillBirkhoffBaseWeight_pos k).le).trans_eq (by ring)) z

theorem norm_hillCorollaryTarget_le (s : ℝ) (hs : 0 ≤ s)
    (z : HillBirkhoffWeightedSpace (SpectralWeight.corollaryWeight s hs)) :
    ‖hillCorollaryTarget s hs z‖ ≤ Real.pi^(SpectralWeight.corollarySplit s)*‖z‖ :=
  RealWeightedNatPair.norm_inclusion_le _ _ _ z

@[simp] theorem hillCorollaryTarget_val (s : ℝ) (hs : 0 ≤ s)
    (z : HillBirkhoffWeightedSpace (SpectralWeight.corollaryWeight s hs)) :
    (hillCorollaryTarget s hs z).val = z.val := by
  funext k
  exact RealWeightedNatPair.inclusion_apply _ _ _ z k

end NLS.KdV
