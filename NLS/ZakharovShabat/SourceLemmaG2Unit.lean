import NLS.ZakharovShabat.SourcePeriodicH1Norm

/-! # G.2 on the unit interval in the exact periodic source norm

The source norm is the Chapter 5 Hilbert Fourier norm with weight
1+|2*pi*n|. The potential, Born operator, and solution are the original
period-one objects. This does not assert the arbitrary-time first inequality
with an unspecified local interval norm.
-/
noncomputable section
open Set MeasureTheory
open NLS.Fourier NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The physical L2 class of the original periodic H1 representative. -/
def sourcePeriodicH1L2Class (a : ScalarDomain 2 × ScalarDomain 2) : IntervalPairL2 :=
  intervalL2OfFunction (sourcePeriodicH1Potential a) (memLp_sourcePeriodicH1Potential a)

/-- The L2 potential class is exactly that of the existing classical curve. -/
theorem sourcePeriodicH1L2Class_eq_classical (a : ScalarDomain 2 × ScalarDomain 2) :
    sourcePeriodicH1L2Class a = continuousPotentialL2Class
      (classicalSobolevPotential (Coeff.periodDoubleSobolev a.1,Coeff.periodDoubleSobolev a.2)) := by
  apply (intervalL2OfFunction_eq_iff _ _ _ _).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact sourcePeriodicH1Potential_eq_classical a ⟨s,hs.1.le,hs.2⟩

/-- Its physical L2 norm is exactly the original source coefficient norm. -/
@[simp] theorem norm_sourcePeriodicH1L2Class (a : ScalarDomain 2 × ScalarDomain 2) :
    ‖sourcePeriodicH1L2Class a‖ = ‖sobolevSourceInclusion a‖ := by
  have h := norm_sq_intervalL2OfFunction (sourcePeriodicH1Potential a) (memLp_sourcePeriodicH1Potential a)
  change ‖sourcePeriodicH1L2Class a‖^2 =
    (∫ s in (0 : ℝ)..1, ‖periodOneSobolevSynthesis a.1 (s : AddCircle (2 : ℝ))‖^2)+
    (∫ s in (0 : ℝ)..1, ‖periodOneSobolevSynthesis a.2 (s : AddCircle (2 : ℝ))‖^2) at h
  rw [integral_sq_periodOneSobolevSynthesis,integral_sq_periodOneSobolevSynthesis] at h
  have hs : ‖sobolevSourceInclusion a‖^2 = ‖scalarInclusion a.1‖^2+‖scalarInclusion a.2‖^2 :=
    WithLp.prod_norm_sq_eq_of_L2 _
  nlinarith [norm_nonneg (sourcePeriodicH1L2Class a),norm_nonneg (sobolevSourceInclusion a)]

/-- The uniform first Born estimate with the exact periodic Fourier norm. -/
theorem sourceLemmaG2_firstBorn_unit (a : ScalarDomain 2 × ScalarDomain 2)
    (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    l2NormalizedHermitianFirstBorn (sourcePeriodicH1L2Class a) z t ≤
      3/(2*‖z‖)*‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ := by
  have h := intervalHermitianFirstBornOperator_weighted_le_unit_H1
    (sourcePeriodicH1Potential a) (memLp_sourcePeriodicH1Potential a)
    (absolutelyContinuous_periodOneSobolevSynthesis a.1)
    (absolutelyContinuous_periodOneSobolevSynthesis a.2)
    (memLp_deriv_periodOneSobolevSynthesis a.1)
    (memLp_deriv_periodOneSobolevSynthesis a.2) z hz t
  rw [intervalHermitianFirstBornOperator_eq_l2] at h
  exact h.trans (mul_le_mul_of_nonneg_left (intervalPairH1Norm_sourcePeriodic_le a) (by positivity))

/-- The unit-interval G.2 remainder estimate in the Chapter 5 periodic norm,
retaining the exact coefficient ||phi||_2 exp(||phi||_2) and 3/(2|z|). -/
theorem sourceLemmaG2_remainder_unit (a : ScalarDomain 2 × ScalarDomain 2)
    (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    l2NormalizedHermitianRemainder (sourcePeriodicH1L2Class a) z t ≤
      3/(2*‖z‖)*(1+‖sobolevSourceInclusion a‖*Real.exp ‖sobolevSourceInclusion a‖)*
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ := by
  let B := 3/(2*‖z‖)*‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖
  have h := l2HermitianRemainder_le_of_firstBorn_uniform_unit (sourcePeriodicH1L2Class a) z B
    (by dsimp [B]; positivity) (sourceLemmaG2_firstBorn_unit a z hz) t
  rw [norm_sourcePeriodicH1L2Class] at h
  exact h.trans_eq (by dsimp [B]; ring)

/-- The same source estimate for the existing actual classical fundamental matrix. -/
theorem sourceLemmaG2_classical_remainder_unit (a : ScalarDomain 2 × ScalarDomain 2)
    (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    classicalNormalizedHermitianRemainder
      (classicalSobolevPotential (Coeff.periodDoubleSobolev a.1,Coeff.periodDoubleSobolev a.2)) z t ≤
      3/(2*‖z‖)*(1+‖sobolevSourceInclusion a‖*Real.exp ‖sobolevSourceInclusion a‖)*
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ := by
  have h := sourceLemmaG2_remainder_unit a z hz t
  rw [sourcePeriodicH1L2Class_eq_classical,l2NormalizedHermitianRemainder_of_continuous] at h
  exact h

end NLS.ZakharovShabat
