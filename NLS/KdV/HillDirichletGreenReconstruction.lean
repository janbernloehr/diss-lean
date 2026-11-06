import NLS.KdV.HillForcedFourierReduction
import NLS.KdV.HillDirichletParityForcing
import NLS.Fourier.UnitIntervalParityUniqueness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory NLS.Fourier NLS.ComplexAnalysis NLS.LinearVolterra
open scoped ENNReal Classical

namespace NLS.KdV



/-- Every parity block of the actual normalized Dirichlet eigenfunction is
nonzero. The proof uses native interval Fourier uniqueness and the actual
strictly positive scalar-state mass, not nontriviality of the full sequence alone. -/
theorem hillL2DirichletParitySequence_ne_zero (q : Coeff 2) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) (r : ℤ) :
    hillL2DirichletParitySequence q energy r ≠ 0 := by
  intro he
  have hcoeff (k : ℤ) : halfCoefficient (hillL2DirichletPosition q energy) (2*k+r) = 0 := by
    have hh := congrArg (fun a : Coeff 1 => a (2*k+r)) he
    rw [hillL2DirichletParitySequence_apply,if_pos (by omega),
      hillL2DirichletHalfSequence_apply q energy hzero] at hh
    simp only [lp.coeFn_zero,Pi.zero_apply] at hh
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  have hf : Continuous (hillL2DirichletPosition q energy) :=
    (continuous_extend (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1))).fst
  have hF := eq_zero_on_unitInterval_of_halfCoefficient_parity_zero
    (hillL2DirichletPosition q energy) hf r hcoeff
  have hmass := hillL2FrequencyStateCurve_mass_pos q (Complex.sqrt energy) (0,1)
    (by intro h; have hh := congrArg Prod.snd h; norm_num at hh)
  have hm0 : scalarStateMass (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1)) = 0 := by
    rw [scalarStateMass_eq_integral]
    calc
      _ = ∫ x in (0 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc (0 : ℝ) 1 := by
          simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
        change normSq (hillL2DirichletPosition q energy x) = 0
        rw [hF hx']
        simp
      _ = 0 := by simp
  linarith

/-- The actual parity sequence in the existing unit-weight reduction space. -/
def hillUnitDirichletParitySequence (q : Coeff 2) (energy : ℂ) (r : ℤ) :
    WeightedCoeff SpectralWeight.one.toWeight 1 :=
  hillUnitWeightLift 1 (hillL2DirichletParitySequence q energy r)

/-- The original Dirichlet solution satisfies the proved boundary-forced
coefficient equation in exactly the reduction's own spaces and normalization. -/
theorem hillUnitDirichletParitySequence_isForced (q : Coeff 2)
    (hq : q ∈ Coeff.paritySubspace 0) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) (r : ℤ) :
    IsHillBoundaryForcedFourierSolution (hillUnitWeightLift 2 q) energy r
      (hillL2DirichletBoundaryJump q energy r) (hillUnitDirichletParitySequence q energy r) := by
  intro k
  simp only [hillUnitDirichletParitySequence,hillUnitWeightLift_apply]
  rw [← hillUnitWeightLift_convolution,hillUnitWeightLift_apply]
  have hh := hillL2DirichletParitySequence_forced_equation q hq energy hzero r k
  by_cases hk : k%2=r%2
  · simpa only [if_pos hk,mul_one] using hh
  · simpa only [if_neg hk,mul_zero,sub_zero] using hh

/-- The actual two raw resonant coefficients; the interval normalization is
retained by the doubled parity projection in this definition. -/
def hillL2DirichletResonantModes (q : Coeff 2) (energy : ℂ) (n : ℕ) : ℂ × ℂ :=
  hillModeCoordinates SpectralWeight.one.toWeight 1 n
    (hillUnitDirichletParitySequence q energy n)

variable (q : Coeff 2) (hq : q ∈ Coeff.paritySubspace 0) (energy : ℂ)
  (hzero : hillL2DirichletCharacteristic q energy = 0) (n : ℕ) (hn : 1 ≤ n)
  (hz : energy ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ))

include hq hzero

/-- Exact Green reconstruction of the original complex Dirichlet solution,
with its own actual endpoint derivative jump. -/
theorem hillUnitDirichletParitySequence_reconstruct :
    hillUnitDirichletParitySequence q energy n =
      hillBoundaryReconstruct (hillUnitWeightLift 2 q) n hn n energy hz
        (by simpa only [norm_hillUnitWeightLift] using hcut)
        (hillL2DirichletResonantModes q energy n) (hillL2DirichletBoundaryJump q energy n) :=
  hillBoundaryForcedFourier_reconstruct (hillUnitWeightLift 2 q) n hn n energy hz
    (by simpa only [norm_hillUnitWeightLift] using hcut)
    (hillL2DirichletBoundaryJump q energy n) (hillUnitDirichletParitySequence q energy n)
    (hillUnitDirichletParitySequence_isForced q hq energy hzero n)

/-- The genuine finite equation for a Dirichlet zero has an additional scalar
source, whose coefficient is the actual derivative jump. -/
theorem hillL2DirichletResonantModes_reduced :
    hillReducedOperator SpectralWeight.one (hillUnitWeightLift 2 q) n hn energy hz
      (by simpa only [norm_hillUnitWeightLift] using hcut) (hillL2DirichletResonantModes q energy n) =
    -(hillL2DirichletBoundaryJump q energy n) •
      (((1,1) : ℂ × ℂ)+hillModeCoordinates SpectralWeight.one.toWeight 2 n
        (hillBoundaryGreenPotential (hillUnitWeightLift 2 q) n hn n energy hz
          (by simpa only [norm_hillUnitWeightLift] using hcut))) := by
  have hh := hillBoundaryForcedFourier_reduced (hillUnitWeightLift 2 q) n hn n energy hz
    (by simpa only [norm_hillUnitWeightLift] using hcut)
    (hillL2DirichletBoundaryJump q energy n) (hillUnitDirichletParitySequence q energy n)
    (hillUnitDirichletParitySequence_isForced q hq energy hzero n)
  simpa [hillL2DirichletResonantModes] using hh

include hn hz hcut in
/-- The augmented finite data cannot both vanish; no false claim that the
resonant pair alone is always nonzero is needed. -/
theorem hillL2DirichletResonantModes_or_jump_ne_zero :
    hillL2DirichletResonantModes q energy n ≠ 0 ∨ hillL2DirichletBoundaryJump q energy n ≠ 0 := by
  by_cases hu : hillL2DirichletResonantModes q energy n = 0
  · right
    intro hJ
    have hh := hillUnitDirichletParitySequence_reconstruct q hq energy hzero n hn hz hcut
    rw [hu,hJ,hillBoundaryReconstruct,map_zero,zero_smul,sub_zero] at hh
    apply hillL2DirichletParitySequence_ne_zero q energy hzero n
    exact (hillUnitWeightLift 1).injective (hh.trans (map_zero _).symm)
  · exact Or.inl hu

/-- The correction to the periodic reconstruction is quantitatively controlled
by the actual boundary jump, uniformly over the high complex strip. -/
theorem norm_hillUnitDirichletParitySequence_sub_reconstruct_le :
    ‖hillUnitDirichletParitySequence q energy n-
      hillReconstruct SpectralWeight.one (hillUnitWeightLift 2 q) n hn energy hz
        (by simpa only [norm_hillUnitWeightLift] using hcut) (hillL2DirichletResonantModes q energy n)‖ ≤
      8*‖hillL2DirichletBoundaryJump q energy n‖ := by
  have hc : 8*‖hillUnitWeightLift 2 q‖ ≤ (n : ℝ) := by
    simpa only [norm_hillUnitWeightLift] using hcut
  have hh := hillUnitDirichletParitySequence_reconstruct q hq energy hzero n hn hz hcut
  have he : hillUnitDirichletParitySequence q energy n-
      hillReconstruct SpectralWeight.one (hillUnitWeightLift 2 q) n hn energy hz hc
        (hillL2DirichletResonantModes q energy n) =
      -(hillL2DirichletBoundaryJump q energy n) •
        hillCorrectedBoundaryGreen (hillUnitWeightLift 2 q) n hn n energy hz hc := by
    rw [hh,hillBoundaryReconstruct,neg_smul]
    abel
  rw [he,norm_smul,norm_neg]
  calc
    _ ≤ ‖hillL2DirichletBoundaryJump q energy n‖*8 :=
      mul_le_mul_of_nonneg_left
        (norm_hillCorrectedBoundaryGreen_le (hillUnitWeightLift 2 q) n hn n energy hz hc) (norm_nonneg _)
    _ = _ := by ring

end NLS.KdV
