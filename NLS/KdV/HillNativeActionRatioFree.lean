import NLS.KdV.HillNativeActionRatioPhysical
import NLS.KdV.HillFreeCoordinateNormalization

/-! # The exact original free normalization of every native action ratio -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillNativeActionGapRatio_zero (k : ℕ+) :
    hillNativeActionGapRatio h0q h0r k 0 = (2*(k : ℂ)*Real.pi)⁻¹ := by
  obtain ⟨η,hη,hphysical⟩ := exists_hillNativeActionGapRatio_all_physical_matching h0q h0r
  let q0 : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  have hcoeff : SpectralWeight.one.toCoeff q0.val = Coeff.periodDouble (0 : Coeff 2) := by
    simp only [q0,map_zero]
  have h := hphysical q0 0 hcoeff (by simpa only [norm_zero] using hη) k
  exact h.trans (hillActionGapRatio_free h0q h0r (k : ℕ) k.property)

theorem hillNativeActionGapRatio_normalized_zero (k : ℕ+) :
    (k : ℂ)*hillNativeActionGapRatio h0q h0r k 0 = (2*(Real.pi : ℂ))⁻¹ := by
  rw [hillNativeActionGapRatio_zero]
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast k.ne_zero
  field_simp

end NLS.KdV
