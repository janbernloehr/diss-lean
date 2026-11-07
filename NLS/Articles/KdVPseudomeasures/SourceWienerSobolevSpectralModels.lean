import NLS.Articles.KdVPseudomeasures.SourceWienerSpectralValues
import NLS.Fourier.PeriodicEqualWeightIsometry

/-! The literal original complex FL^(N,1) source and Sobolev ell-one
target are isometrically identical to the general Wiener spectral models. -/
noncomputable section
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
namespace NLS.Articles.KdVPseudomeasures

def sourceWienerSobolevWeight (N : ℕ) : SpectralWeight := SpectralWeight.sobolev (N:ℝ) (by positivity)

theorem sourceWienerSobolevWeight_eq (N : ℕ) :
    (sourceWienerSobolevWeight N).toWeight = Weight.sobolev (N:ℝ) := by
  apply Weight.eq_of_values
  intro k
  exact SpectralWeight.sobolev_apply (N:ℝ) (by positivity) k

theorem sourceWienerSobolevWeight_negative_zero (N : ℕ) :
    (sourceWienerSobolevWeight N).negativeSobolev 0 = Weight.sobolev (N:ℝ) := by
  apply Weight.eq_of_values
  intro k
  simp only [SpectralWeight.negativeSobolev_apply,Weight.sobolev_zero_apply,div_one,
    sourceWienerSobolevWeight,SpectralWeight.sobolev_apply]

def sourceWienerSobolevInput (N : ℕ) :
    FourierLebesgueSpace (2:ℝ) (N:ℝ) 1 ≃ₗᵢ[ℂ]
      PeriodicFourierLebesgue (2:ℝ) ((sourceWienerSobolevWeight N).negativeSobolev 0) 1 :=
  PeriodicFourierLebesgue.equalWeightIsometry 1 _ _ (sourceWienerSobolevWeight_negative_zero N).symm

theorem sourceWienerSobolevInput_val (N : ℕ) (q : FourierLebesgueSpace (2:ℝ) (N:ℝ) 1) :
    (sourceWienerSobolevInput N q).val = q.val :=
  PeriodicFourierLebesgue.equalWeightIsometry_val 1 _ _ _ q

def sourceWienerSobolevGapValues (N : ℕ) (q : FourierLebesgueSpace (2:ℝ) (N:ℝ) 1) (k : ℤ) : ℂ :=
  sourceWienerGapValues (sourceWienerSobolevWeight N) (sourceWienerSobolevInput N q) k

def sourceWienerSobolevMidpointValues (N : ℕ) (q : FourierLebesgueSpace (2:ℝ) (N:ℝ) 1)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) (k : ℤ) : ℂ :=
  sourceWienerMidpointValues (sourceWienerSobolevWeight N) (sourceWienerSobolevInput N q)
    (by rw [sourceWienerSobolevInput_val]; exact hp) k

/-- The canonical labels see the same entire original physical distribution. -/
theorem sourceWienerSobolevPlain_same_distribution (N : ℕ) (q : FourierLebesgueSpace (2:ℝ) (N:ℝ) 1) :
    (sourceWienerPlain (sourceWienerSobolevWeight N) (sourceWienerSobolevInput N q)).val = q.val :=
  (sourceWienerPlain_val _ _).trans (sourceWienerSobolevInput_val N q)

end NLS.Articles.KdVPseudomeasures
