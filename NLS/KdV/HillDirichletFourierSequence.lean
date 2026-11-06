import NLS.KdV.HillDirichletForcedFourier
import NLS.Fourier.ZeroBoundarySummableCoefficients
import NLS.SequenceSpaces.FunctionOrZero

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.Fourier NLS.FunctionalAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



/-- The Fourier coefficients of an actual rough Dirichlet eigenfunction
have one full Hilbert derivative even when its endpoint derivatives differ. -/
theorem memlp_sobolev_hillL2DirichletHalfCoefficient (q : Coeff 2) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) :
    Memℓp (fun k : ℤ => (Weight.sobolev 1 k : ℂ)*hillL2DirichletHalfCoefficient q energy k) 2 := by
  have hA := absolutelyContinuousOnInterval_hillStateCurve q (Complex.sqrt energy) (0,1)
  have hf := absolutelyContinuousOnInterval_clm hA (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hf2 := memLp_two_interval
    (continuous_extend (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1))).fst 0 1 (by norm_num)
  have hg2 := memLp_two_interval
    (continuous_extend (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1))).snd 0 1 (by norm_num)
  exact memlp_sobolev_halfCoefficient_of_ac_zero_boundary
    (hillL2DirichletPosition q energy) (hillL2DirichletMomentum q energy) hf hf2 hg2
    (ae_hasDerivAt_hillL2FrequencyStateCurve_fst q (Complex.sqrt energy) (0,1))
    (hillL2DirichletPosition_zero q energy) ((hillL2DirichletPosition_one q energy).trans hzero)

/-- A total sequence constructor; exact coordinate recovery is proved at the
actual Dirichlet zeros, where absolute convergence has been established. -/
def hillL2DirichletHalfSequence (q : Coeff 2) (energy : ℂ) : Coeff 1 :=
  Coeff.ofFunctionOrZero 1 (hillL2DirichletHalfCoefficient q energy)

theorem hillL2DirichletHalfSequence_apply (q : Coeff 2) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) (k : ℤ) :
    hillL2DirichletHalfSequence q energy k = hillL2DirichletHalfCoefficient q energy k := by
  let a : WeightedCoeff (Weight.sobolev 1) 2 :=
    ⟨hillL2DirichletHalfCoefficient q energy,memlp_sobolev_hillL2DirichletHalfCoefficient q energy hzero⟩
  have ha (j : ℤ) : WeightedCoeff.sobolevToL1CLM 2 (by simp) a j =
      hillL2DirichletHalfCoefficient q energy j :=
    WeightedCoeff.sobolevToL1CLM_apply 2 (by simp) a j
  rw [hillL2DirichletHalfSequence,Coeff.ofFunctionOrZero_eq_of_coordinates _ _ ha]
  exact ha k

theorem summable_norm_hillL2DirichletHalfCoefficient (q : Coeff 2) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) :
    Summable (fun k : ℤ => ‖hillL2DirichletHalfCoefficient q energy k‖) := by
  simpa only [hillL2DirichletHalfSequence_apply q energy hzero] using
    (lp.memℓp (hillL2DirichletHalfSequence q energy)).norm.summable_of_one

/-- The genuine summable sequence satisfies the original forced Fourier
identity at every frequency, including zero and the two resonant modes. -/
theorem hillL2DirichletHalfSequence_forced_equation (q : Coeff 2) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) (k : ℤ) :
    (energy-(freeHillValue k : ℂ))*hillL2DirichletHalfSequence q energy k =
      halfCoefficient (fun x => hillL2ScalarRepresentative q x*hillL2DirichletPosition q energy x) k -
        (hillL2DirichletSlope q energy*wave (-k) 1-1)/2 := by
  rw [hillL2DirichletHalfSequence_apply q energy hzero]
  exact hillL2DirichletHalfCoefficient_forced_equation q energy hzero k

end NLS.KdV
