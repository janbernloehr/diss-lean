import NLS.KdV.HillDirichletGreenReconstruction
import NLS.KdV.HillReconstructionBoundary
import NLS.Fourier.SignedIntervalH1Extension

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory NLS.Fourier NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal Classical

namespace NLS.KdV



/-- The actual rough Dirichlet position belongs to the full interval H1 class;
no matching of its endpoint derivatives is required. -/
theorem hasIntervalH1_hillL2DirichletPosition (q : Coeff 2) (energy : ℂ) :
    HasIntervalH1Regularity (hillL2DirichletPosition q energy) := by
  have hA := absolutelyContinuousOnInterval_hillStateCurve q (Complex.sqrt energy) (0,1)
  have hf := absolutelyContinuousOnInterval_clm hA (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hg := memLp_two_interval
    (continuous_extend (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1))).snd 0 1 (by norm_num)
  refine ⟨hf,?_⟩
  apply (memLp_congr_ae ?_).mpr hg
  filter_upwards [ae_hasDerivAt_hillL2FrequencyStateCurve_fst q (Complex.sqrt energy) (0,1)] with x hx
  exact hx.deriv

/-- The actual parity coefficients synthesize the original Dirichlet position
everywhere on its closed interval, not only almost everywhere. -/
theorem continuousSynthesis_hillL2DirichletParitySequence_on_unit (q : Coeff 2) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) (r : ℤ) :
    EqOn (fun x : ℝ => continuousSynthesis (hillL2DirichletParitySequence q energy r)
      (x : AddCircle (2 : ℝ))) (hillL2DirichletPosition q energy) (Icc (0 : ℝ) 1) := by
  let f := hillL2DirichletPosition q energy
  have hf : HasIntervalH1Regularity f := hasIntervalH1_hillL2DirichletPosition q energy
  have hend : f 1 = wave r 1*f 0 := by
    simp only [f,hillL2DirichletPosition_zero,hillL2DirichletPosition_one,hzero,mul_zero]
  let b := signedSobolevCoefficients r f hf hend
  have he : hillL2DirichletParitySequence q energy r = WeightedCoeff.sobolevToL1CLM 2 (by simp) b := by
    ext k
    rw [hillL2DirichletParitySequence_apply,hillL2DirichletHalfSequence_apply q energy hzero,
      WeightedCoeff.sobolevToL1CLM_apply]
    change (if k%2=r%2 then 2*halfCoefficient f k else 0) =
      (signedSobolevCoefficients r f hf hend).val k
    rw [signedSobolevCoefficients_apply]
    by_cases hk : k%2=r%2
    · rw [if_pos hk,periodTwoCoefficient_signedDouble_of_intervalIntegrable (wave r 1)
        hf.1.continuousOn.intervalIntegrable,hillBoundaryWave_eq_of_parity k r hk,← wave_add,
        add_neg_cancel,wave_zero]
      ring
    · rw [if_neg hk,periodTwoCoefficient_signedDouble_parity_of_intervalIntegrable r
        hf.1.continuousOn.intervalIntegrable k hk]
  intro x hx
  rw [he]
  change sobolevSynthesis (by simp) b (x : AddCircle (2 : ℝ)) = f x
  rw [sobolevSynthesis_signedSobolevCoefficients r f hf hend
    (show x ∈ Icc (0 : ℝ) 2 from ⟨hx.1,hx.2.trans (by norm_num)⟩)]
  exact signedDouble_left _ _ hx.2

theorem continuousSynthesis_hillL2DirichletParitySequence_zero (q : Coeff 2) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) (r : ℤ) :
    continuousSynthesis (hillL2DirichletParitySequence q energy r) 0 = 0 :=
  ((continuousSynthesis_hillL2DirichletParitySequence_on_unit q energy hzero r) (by simp)).trans
    (hillL2DirichletPosition_zero q energy)

/-- Original physical boundary evaluation on the unit-weight coefficient space. -/
def hillUnitBoundaryTrace : WeightedCoeff SpectralWeight.one.toWeight 1 →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ (0 : AddCircle (2 : ℝ))).comp
    (Fourier.continuousSynthesisCLM.comp SpectralWeight.one.toCoeff)

/-- The actual corrected boundary Green value at the base point. -/
def hillBoundaryGreenTrace (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (r : ℤ) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) : ℂ :=
  hillUnitBoundaryTrace (hillCorrectedBoundaryGreen q n hn r z hz hcut)

/-- The scalar boundary equation completing the two forced resonant rows. -/
theorem hillBoundaryReconstruct_trace_zero_iff
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (r : ℤ)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) (u : ℂ × ℂ) (J : ℂ) :
    hillUnitBoundaryTrace (hillBoundaryReconstruct q n hn r z hz hcut u J) = 0 ↔
      hillReconstructionBoundaryRow SpectralWeight.one n (q,z) u =
        J*hillBoundaryGreenTrace q n hn r z hz hcut := by
  have he : hillUnitBoundaryTrace (hillReconstruct SpectralWeight.one q n hn z hz hcut u) =
      hillReconstructionBoundaryRow SpectralWeight.one n (q,z) u := by
    unfold hillReconstructionBoundaryRow hillReconstructedCurveFamily
    rw [hillReconstructionFamily_eq SpectralWeight.one n hn (q,z) hz hcut]
    rfl
  rw [hillBoundaryReconstruct,map_sub,map_smul,he,sub_eq_zero]
  rfl

theorem norm_hillBoundaryGreenTrace_le
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (r : ℤ)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    ‖hillBoundaryGreenTrace q n hn r z hz hcut‖ ≤ 8 := by
  calc
    _ ≤ ‖Fourier.continuousSynthesis (SpectralWeight.one.toCoeff
      (hillCorrectedBoundaryGreen q n hn r z hz hcut))‖ := ContinuousMap.norm_coe_le_norm _ _
    _ ≤ ‖SpectralWeight.one.toCoeff (hillCorrectedBoundaryGreen q n hn r z hz hcut)‖ :=
      Fourier.norm_continuousSynthesis_le _
    _ ≤ ‖hillCorrectedBoundaryGreen q n hn r z hz hcut‖ := SpectralWeight.one.norm_toCoeff_le _
    _ ≤ 8 := norm_hillCorrectedBoundaryGreen_le q n hn r z hz hcut

/-- The original Dirichlet data satisfy this scalar boundary equation together
with their nontrivial augmented finite resonant system. -/
theorem hillL2DirichletResonantModes_boundary_equation
    (q : Coeff 2) (hq : q ∈ Coeff.paritySubspace 0) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) (n : ℕ) (hn : 1 ≤ n)
    (hz : energy ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    hillReconstructionBoundaryRow SpectralWeight.one n (hillUnitWeightLift 2 q,energy)
        (hillL2DirichletResonantModes q energy n) =
      hillL2DirichletBoundaryJump q energy n*
        hillBoundaryGreenTrace (hillUnitWeightLift 2 q) n hn n energy hz
          (by simpa only [norm_hillUnitWeightLift] using hcut) := by
  have hc : 8*‖hillUnitWeightLift 2 q‖ ≤ (n : ℝ) := by simpa only [norm_hillUnitWeightLift] using hcut
  have hb : hillUnitBoundaryTrace (hillUnitDirichletParitySequence q energy n) = 0 := by
    change continuousSynthesis (SpectralWeight.one.toCoeff
      (hillUnitWeightLift 1 (hillL2DirichletParitySequence q energy n))) 0 = 0
    rw [toCoeff_hillUnitWeightLift]
    exact continuousSynthesis_hillL2DirichletParitySequence_zero q energy hzero n
  rw [hillUnitDirichletParitySequence_reconstruct q hq energy hzero n hn hz hcut] at hb
  exact (hillBoundaryReconstruct_trace_zero_iff (hillUnitWeightLift 2 q) n hn n energy hz hc
    (hillL2DirichletResonantModes q energy n) (hillL2DirichletBoundaryJump q energy n)).mp hb

end NLS.KdV
