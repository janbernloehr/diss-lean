import NLS.ZakharovShabat.L2PeriodicFundamental
import NLS.ZakharovShabat.SourcePhysicalL2
import NLS.ZakharovShabat.HilbertDiscriminant
import NLS.SequenceSpaces.FiniteSourceDensity

/-! # The canonical discriminant is the actual L2 monodromy trace

The finite Fourier comparison extends by density and continuity in the
original physical L2 norm. The result requires no continuous representative.
-/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The physical discriminant is the trace of the actual L2 monodromy. -/
def l2Discriminant (u : IntervalPairL2) (z : ℂ) : ℂ := (l2Monodromy u z).trace

/-- Exact recovery of the original continuous-potential monodromy. -/
theorem l2Monodromy_of_continuous (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    l2Monodromy (continuousPotentialL2Class Φ) z = classicalMonodromy Φ z :=
  l2FundamentalMatrix_of_continuous Φ z _

theorem l2Discriminant_of_continuous (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    l2Discriminant (continuousPotentialL2Class Φ) z = classicalDiscriminant Φ z := by
  unfold l2Discriminant classicalDiscriminant
  rw [l2Monodromy_of_continuous]

/-- Joint complex analyticity in the frequency and the original physical L2 potential. -/
theorem analyticOnNhd_l2Discriminant_joint :
    AnalyticOnNhd ℂ (fun q : ℂ × IntervalPairL2 => l2Discriminant q.2 q.1) univ := by
  intro q _
  have h := analyticOnNhd_l2Monodromy_joint q (mem_univ _)
  unfold l2Discriminant Matrix.trace
  exact Finset.analyticAt_fun_sum _ (fun i _ =>
    analyticAt_pi_iff.mp (analyticAt_pi_iff.mp h i) i)

theorem continuous_l2Discriminant_joint :
    Continuous (fun q : ℂ × IntervalPairL2 => l2Discriminant q.2 q.1) :=
  continuous_iff_continuousAt.mpr (fun q => (analyticOnNhd_l2Discriminant_joint q (mem_univ _)).continuousAt)

/-- Every original Hilbert source has its canonical discriminant equal to the physical monodromy trace. -/
theorem canonicalDiscriminant_eq_l2_source (φ : CoeffPair 2) (z : ℂ) :
    canonicalDiscriminant (by simp) (periodOnePotential φ) z = l2Discriminant (sourcePhysicalL2 φ) z := by
  have hF : Continuous (fun ψ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential ψ) z) := by
    have hc : Continuous (fun ψ : CoeffPair 2 => (z,ψ)) := continuous_const.prodMk continuous_id
    have h := (analyticOnNhd_canonicalDiscriminant_periodOne (p := 2) (by simp) (by norm_num)).continuousOn
    have hcont := continuousOn_univ.mp h
    have hcomp := hcont.comp hc
    exact hcomp
  have hG : Continuous (fun ψ : CoeffPair 2 => l2Discriminant (sourcePhysicalL2 ψ) z) := by
    have hc : Continuous (fun ψ : CoeffPair 2 => (z,sourcePhysicalL2 ψ)) :=
      continuous_const.prodMk sourcePhysicalL2.continuous
    have h := continuous_l2Discriminant_joint.comp hc
    exact h
  have he := CoeffPair.eq_of_continuous_of_finsupp (p := 2) (by simp) _ _ hF hG (fun a => by
    rw [sourcePhysicalL2_ofFinsupp,l2Discriminant_of_continuous]
    exact canonicalDiscriminant_eq_classical _ (periodOnePotential_mem _) _
      (finiteSource_physical_compatibility a).1 z)
  exact congrFun he φ

/-- The trace identity holds for every even-supported Hilbert coefficient potential. -/
theorem canonicalDiscriminant_eq_l2 (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    canonicalDiscriminant (by simp) φ z = l2Discriminant (physicalRestrictionL2 φ) z := by
  have hr : φ ∈ (periodOnePotential (p := 2)).range := by rw [range_periodOnePotential]; exact hφ
  obtain ⟨ψ,rfl⟩ := hr
  exact canonicalDiscriminant_eq_l2_source ψ z

/-- The actual L2 trace has the already normalized full periodic spectral product. -/
theorem canonicalPeriodicProduct_eq_l2Discriminant (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    canonicalPeriodicProduct (by simp) φ z = (l2Discriminant (physicalRestrictionL2 φ) z)^2-4 := by
  rw [canonicalPeriodic_eq_discriminant_sq_sub_four φ hφ,canonicalDiscriminant_eq_l2 φ hφ]

/-- The actual L2 monodromy trace detects the entire original periodic spectrum. -/
theorem l2Discriminant_sq_eq_four_iff (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    (l2Discriminant (physicalRestrictionL2 φ) z)^2 = 4 ↔ z ∈ periodicSpectrum (by simp) φ := by
  rw [← canonicalDiscriminant_eq_l2 φ hφ]
  exact canonicalDiscriminant_sq_eq_four_iff φ hφ z

/-- The separate trace levels retain the original even and odd algebraic multiplicities. -/
theorem l2Discriminant_parity_levels (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    (l2Discriminant (physicalRestrictionL2 φ) z = 2 ↔ 0 < parityAlgebraicMultiplicity (by simp) φ 0 z) ∧
    (l2Discriminant (physicalRestrictionL2 φ) z = -2 ↔ 0 < parityAlgebraicMultiplicity (by simp) φ 1 z) := by
  rw [← canonicalDiscriminant_eq_l2 φ hφ]
  exact canonicalDiscriminant_parity_levels φ hφ z

/-- The physical L2 discriminant retains the original free normalization. -/
@[simp] theorem l2Discriminant_zero (z : ℂ) : l2Discriminant 0 z = freeDiscriminant z := by
  have h := canonicalDiscriminant_eq_l2_source 0 z
  simpa only [map_zero,canonicalDiscriminant_zero] using h.symm

end NLS.ZakharovShabat
