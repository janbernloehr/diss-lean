import NLS.KdV.HillHminusOneSingularPotential
import NLS.KdV.SingularHillDenseSpectrum
import NLS.ComplexAnalysis.ClosedZeroGraphPersistence

/-! # The entire H^-1 characteristic detects the full original Hill spectrum

Both directions are proved on all complex unit-period H^-1 potentials.
Dense physical L2 comparison extends to characteristic zeros by joint
closedness and finite-order zero persistence, and to physical spectral
points by persistence of nonzero Riesz projection ranks. No simple-root,
reality, finite-mode, or high-energy hypothesis is imposed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ComplexAnalysis

theorem continuous_hillHminusRadicand_uncurry : Continuous (Function.uncurry hillHminusRadicand) := by
  have h := analyticOnNhd_hillHminusRadicand_joint.continuous.comp
    (continuous_snd.prodMk continuous_fst : Continuous (fun p : PeriodOneHminusOne × ℂ => (p.2,p.1)))
  exact h

theorem periodOneSingularHillSpectrum_iff_characteristic
    (q : PeriodOneHminusOne) (z : ℂ) :
    z ∈ singularHillSpectrum (periodOneSingularPotential q) ↔ hillHminusRadicand q z = 0 := by
  constructor
  · intro hz
    apply singularHillSpectrum_constraint_of_dense_parameters periodOneSingularPotential
      periodOneSingularPotential.continuous hillHminusRadicand continuous_hillHminusRadicand_uncurry
      (range periodOneL2Inclusion) denseRange_periodOneL2Inclusion _ q z hz
    rintro p ⟨a,rfl⟩ w hw
    exact (periodOneSingularPotential_L2_spectrum a w).mp hw
  · intro hz
    obtain ⟨b,hb⟩ := exists_hillHminusRadicand_ne_zero q
    apply zero_pair_mem_closed_of_closure_parameters hillHminusRadicand continuous_hillHminusRadicand_uncurry
      (fun p w _ => (analyticOnNhd_hillHminusRadicand_joint (w,p) (mem_univ _)).comp
        (f := fun w : ℂ => (w,p)) (analyticAt_id.prod analyticAt_const))
      (range periodOneL2Inclusion)
      {p : PeriodOneHminusOne × ℂ | p.2 ∈ singularHillSpectrum (periodOneSingularPotential p.1)}
      isClosed_periodOneSingularHillSpectralGraph _ q (denseRange_periodOneL2Inclusion q) b hb z hz
    rintro p ⟨a,rfl⟩ w hw
    exact (periodOneSingularPotential_L2_spectrum a w).mpr hw

theorem periodOneSingularHillResolvent_iff_characteristic_ne_zero
    (q : PeriodOneHminusOne) (z : ℂ) :
    z ∈ singularHillResolventSet (periodOneSingularPotential q) ↔ hillHminusRadicand q z ≠ 0 := by
  simpa only [singularHillSpectrum,mem_compl_iff,not_not] using
    not_congr (periodOneSingularHillSpectrum_iff_characteristic q z)

theorem hillHminusRadicand_zero_iff_original_H1_eigenvector
    (q : PeriodOneHminusOne) (z : ℂ) :
    hillHminusRadicand q z = 0 ↔
      ∃ f : FourierLebesgueSpace (2 : ℝ) 1 2, f ≠ 0 ∧
        singularHillOperator (periodOneSingularPotential q) f = z • singularHillDomainInclusion f := by
  rw [← periodOneSingularHillSpectrum_iff_characteristic,mem_singularHillSpectrum_iff]

theorem periodOneSingularHillSpectrum_im_zero_of_real
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (z : ℂ)
    (hz : z ∈ singularHillSpectrum (periodOneSingularPotential q)) : z.im = 0 :=
  hillHminusRadicand_root_im_zero q hr z ((periodOneSingularHillSpectrum_iff_characteristic q z).mp hz)

end NLS.KdV
