import NLS.ZakharovShabat.SourceDirichletSpectralFlow
import NLS.ZakharovShabat.SourceAngularThetaThetaLocalTransport

/-! # All-time actual spectral transport of the angle/angle bracket

The constructed complete Hilbert spectral flow preserves every actual
periodic gap. Two initially open angle gaps therefore stay in the common
angle domain at every real time. The full actual angle/angle bracket is
constant along this flow, for every selected spectral index.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
namespace SourceAngularThetaCommonDomainData
variable {W₀ B W : Set (CoeffPair 2)}
  {s : (j : ℤ) → CoeffPair 2 → DeletedCoeff 2 j}

/-- The full actual angle/angle bracket is transported unchanged by
the constructed complete Hilbert flow at every real time. Only the two
angle gaps need initially be open; the selected flow gap may collapse. -/
theorem thetaTheta_sourceDirichletSpectralFlow
    (D : SourceAngularThetaCommonDomainData (p := 2) (by simp) (by norm_num) W₀ B W s)
    (k n m : ℤ) (φ : realTypeSourceLocus 2) (t : ℝ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    sourceAngularThetaThetaBracket (by simp) (by norm_num) (by norm_num) n m s
      (sourceDirichletSpectralFlow k φ t).val =
    sourceAngularThetaThetaBracket (by simp) (by norm_num) (by norm_num) n m s φ.val := by
  let γ := sourceDirichletSpectralGlobalCurve k φ
  change sourceAngularThetaThetaBracket (by simp) (by norm_num) (by norm_num) n m s (γ t) =
    sourceAngularThetaThetaBracket (by simp) (by norm_num) (by norm_num) n m s φ.val
  have hzero : γ 0 = φ.val := sourceDirichletSpectralGlobalCurve_zero k φ
  let a : ℝ := min t 0-1
  let b : ℝ := max t 0+1
  have ht : t ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_left t 0],
    by dsimp [b]; linarith [le_max_left t 0]⟩
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_right t 0],
    by dsimp [b]; linarith [le_max_right t 0]⟩
  simpa only [hzero] using
    (D.thetaTheta_eq_on_sourceDirichletSpectral_integralCurve_of_initial_open
      (by norm_num) k n m γ a b
      (fun u _ => sourceDirichletSpectralGlobalCurve_realType k φ u)
      (fun u _ => hasDerivAt_sourceDirichletSpectralGlobalCurve k φ u) 0 t h0 ht
      (by simpa only [hzero] using hn) (by simpa only [hzero] using hm)).symm

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
