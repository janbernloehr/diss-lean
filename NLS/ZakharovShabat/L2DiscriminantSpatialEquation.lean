import NLS.ZakharovShabat.DiscriminantGradientStateAlgebra
import NLS.ZakharovShabat.L2CharacteristicGradients
import NLS.ZakharovShabat.L2SolutionDifferentialEquation

/-! # The actual discriminant gradient's spatial equation at every L2 source

The physical gradient is the proved Fréchet gradient of the actual monodromy
trace. Its adjugate polynomial supplies the spatial equation almost everywhere
without a nonzero monodromy-entry hypothesis. The scalar transport sign is
fixed here by the physical first-order equation and the unconjugated gradient.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

def l2DiscriminantXi (u : IntervalPairL2) (z : ℂ) (x : ℝ) : ℂ :=
  discriminantXiState (l2Monodromy u z)
    (extend (l2SolutionCurve u z (1,0)) x) (extend (l2SolutionCurve u z (0,1)) x)

theorem l2DiscriminantGradient_eq_state (u : IntervalPairL2) (z : ℂ) (x : ℝ) :
    l2DiscriminantGradient u z x = discriminantGradientState (l2Monodromy u z)
      (extend (l2SolutionCurve u z (1,0)) x) (extend (l2SolutionCurve u z (0,1)) x) := by
  have hone : (1 : Icc (0:ℝ) 1) = ⟨1,by norm_num⟩ := by
    apply Subtype.ext
    norm_num
  apply Prod.ext <;>
    dsimp [l2DiscriminantGradient,l2EndpointGradient,discriminantGradientState,
      l2Monodromy,l2FundamentalMatrix] <;> rw [hone] <;> ring

theorem ae_hasDerivAt_l2DiscriminantGradient (u : IntervalPairL2) (z : ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
      HasDerivAt (l2DiscriminantGradient u z)
        (2*I*z*(l2DiscriminantGradient u z x).1+l2DiscriminantXi u z x*(intervalL2Representative u x).2,
         -2*I*z*(l2DiscriminantGradient u z x).2-l2DiscriminantXi u z x*(intervalL2Representative u x).1) x := by
  filter_upwards [ae_hasDerivAt_l2SolutionCurve u z (1,0),
    ae_hasDerivAt_l2SolutionCurve u z (0,1)] with x ha hb
  have h := hasDerivAt_discriminantGradientState (l2Monodromy u z) _ _ _ z x ha hb
  simpa only [← l2DiscriminantGradient_eq_state,l2DiscriminantXi] using h

theorem ae_hasDerivAt_l2DiscriminantXi (u : IntervalPairL2) (z : ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
      HasDerivAt (l2DiscriminantXi u z)
        (2*(intervalL2Representative u x).1*(l2DiscriminantGradient u z x).1-
         2*(intervalL2Representative u x).2*(l2DiscriminantGradient u z x).2) x := by
  filter_upwards [ae_hasDerivAt_l2SolutionCurve u z (1,0),
    ae_hasDerivAt_l2SolutionCurve u z (0,1)] with x ha hb
  have h := hasDerivAt_discriminantXiState (l2Monodromy u z) _ _ _ z x ha hb
  have he : (fun y => discriminantXiState (l2Monodromy u z)
      (extend (l2SolutionCurve u z (1,0)) y) (extend (l2SolutionCurve u z (0,1)) y)) =
      l2DiscriminantXi u z := rfl
  rw [he] at h
  simpa only [← l2DiscriminantGradient_eq_state] using h

theorem l2DiscriminantXi_zero (u : IntervalPairL2) (z : ℂ) :
    l2DiscriminantXi u z 0 = (l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1 := by
  have hz (v : ℂ × ℂ) : extend (l2SolutionCurve u z v) 0 = v := by
    exact (extend_coe (l2SolutionCurve u z v) ⟨0,by norm_num⟩).trans
      (l2SolutionCurve_zero u z v)
  simp [l2DiscriminantXi,discriminantXiState,hz]

end NLS.ZakharovShabat
