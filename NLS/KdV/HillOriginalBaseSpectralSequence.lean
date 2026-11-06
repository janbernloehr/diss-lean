import NLS.KdV.HillOriginalCartesianGermContinuation
import NLS.KdV.HillWeightedSpectralSequence
import NLS.KdV.HillOriginalQuadraticTrace

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- Literal even-index restriction into native unit-period real coordinates. -/
def hillOriginalNativeRealSource (q : RealPeriodOneHillPotential) :
    RealHillWeightedPotential SpectralWeight.one :=
  ⟨hillPeriodOneRestriction SpectralWeight.one q.val,
    hillPeriodOneRestriction_real SpectralWeight.one q.val q.property.2⟩

theorem hillRealWeightedEmbedding_original_native (q : RealPeriodOneHillPotential) :
    hillRealWeightedEmbedding SpectralWeight.one (hillOriginalNativeRealSource q) = q := by
  apply Subtype.ext
  exact hillPeriodOneUnitPotential_restriction_even q.val q.property.1

/-- The ORIGINAL weighted Cartesian sequence in base Hilbert target coordinates.
Its k-th entry is exactly sqrt(2*pi*(k+1)) times the full physical Cartesian. -/
def hillOriginalBaseSpectralSequence (q : RealPeriodOneHillPotential) : lp (fun _ : ℕ => ℂ) 2 :=
  hillWeightedSpectralSequence (by simp) (by intro k; simp) SpectralWeight.one
    (hillOriginalNativeRealSource q)

theorem hillOriginalBaseSpectralSequence_apply (q : RealPeriodOneHillPotential) (k : ℕ) :
    hillOriginalBaseSpectralSequence q k = (Real.sqrt (2*Real.pi*(k+1 : ℕ)) : ℂ) *
      hillSignedSpectralCartesian true ⟨k+1,by omega⟩ q := by
  change hillWeightedSpectralCoordinate SpectralWeight.one (hillOriginalNativeRealSource q) k = _
  simp only [hillWeightedSpectralCoordinate,SpectralWeight.one_apply,ofReal_one,one_mul,
    hillRealWeightedEmbedding_original_native,hillSignedSpectralCartesian,ite_true]
  rfl

/-- The exact base quadratic trace preserves the ORIGINAL mean-zero L2 norm. -/
theorem norm_hillOriginalBaseSpectralSequence (q : RealPeriodOneHillPotential)
    (hmean : q.val.val 0 = 0) : ‖hillOriginalBaseSpectralSequence q‖ = ‖q.val‖ := by
  have hnorm := norm_hillWeightedSpectralSequence_sq (by simp) (by intro k; simp)
    SpectralWeight.one (hillOriginalNativeRealSource q)
  have hpmean : (hillOriginalNativeRealSource q).val.val 0 = 0 := by
    simpa only [hillOriginalNativeRealSource,hillPeriodOneRestriction_apply,mul_zero] using hmean
  rw [tsum_hillWeightedActionTerm_quadratic_l2 _ hpmean] at hnorm
  have hp : ‖(hillOriginalNativeRealSource q).val‖ = ‖q.val‖ :=
    norm_hillPeriodOneRestriction_even SpectralWeight.one q.val q.property.1
  change ‖hillOriginalBaseSpectralSequence q‖^2 = _ at hnorm
  rw [hp] at hnorm
  nlinarith [norm_nonneg (hillOriginalBaseSpectralSequence q),norm_nonneg q.val]

/-- Every coordinate of the actual base spectral sequence passes through
strong H-minus-one source limits, including closed gaps. -/
theorem hillOriginalBaseSpectralSequence_apply_tendsto_of_hminus
    (q : RealPeriodOneHillPotential) (a : ℕ → RealPeriodOneHillPotential)
    (ha : Tendsto (fun j => hillOriginalHminusSource (a j).val) atTop
      (𝓝 (hillOriginalHminusSource q.val))) (k : ℕ) :
    Tendsto (fun j => hillOriginalBaseSpectralSequence (a j) k) atTop
      (𝓝 (hillOriginalBaseSpectralSequence q k)) := by
  simp only [hillOriginalBaseSpectralSequence_apply]
  exact (hillSignedSpectralCartesian_tendsto_of_original_hminus q ⟨k+1,by omega⟩ true a ha).const_mul _

end NLS.KdV
