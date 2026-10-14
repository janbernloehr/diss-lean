import NLS.ZakharovShabat.SourceGapFunctional
import NLS.ZakharovShabat.SourceLocalGapContourZeros
import NLS.ZakharovShabat.SourcePsiSelectedKernelGapZeroSequence

/-!
# The local zero-contour implication on an original disk

A numerator analytic near the filled original disk and real on the
selected real gap has a zero in that gap when Aₘⁿ vanishes, m≠n.
Any nonzero winding suffices. These are the local disk and circuit
ingredients of Lemma 12.2; no entire extension of the numerator is used.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The zero-contour implication for both open and collapsed real gaps. -/
theorem SourceCriticalRootPeriodCircle.localNumerator_zero_of_circle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hψ : IsRealType (CoeffPair.toMax p ψ)) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (D.center:ℂ) D.radius))
    (hreal : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ m, (f z).im = 0)
    (hz : (∮ z in C((D.center:ℂ),D.radius), f z/sourceCanonicalRoot hp hp1 ψ z) = 0) :
    ∃ z ∈ sourcePeriodicSegment hp hp1 ψ m, f z = 0 := by
  rcases sourcePeriodicGap_eq_zero_or_open hp hp1 ψ hψ m with hg | ho
  · refine ⟨sourceStandardRootMidpoint hp hp1 ψ m,sourcePeriodicMidpoint_mem_segment hp hp1 ψ m,?_⟩
    exact sourceLocalNumerator_zero_at_collapsedGap hp hp1 ψ hψ m f hg
      (D.center:ℂ) D.radius D.radius_pos hf
      (D.gap (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m))
      D.closedBall_subset_omittedDomain D.sphere_subset_rootDomain hz
  · obtain ⟨z,hzgap,hzero⟩ := exists_sourceLocalNumerator_zero_on_openGap hp hp1 ψ hψ m f
      hreal ho D.center D.radius D.radius_pos hf D.gap
      D.closedBall_subset_omittedDomain D.sphere_subset_rootDomain hz
    exact ⟨z,sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 ψ m hzgap,hzero⟩

/-- Aₘⁿf=0 forces a gap zero for a local analytic numerator on an original disk.
The circuit may have any nonzero winding, including reversed orientation. -/
theorem SourceCriticalRootPeriodCircle.localNumerator_zero_of_functional
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hψ : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (hmn : m ≠ n) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (D.center:ℂ) D.radius))
    (hreal : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ m, (f z).im = 0)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m))
    (hw : Γ.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) ≠ 0)
    (hz : sourceGapFunctional hp hp1 n m ψ Γ f = 0) :
    ∃ z ∈ sourcePeriodicSegment hp hp1 ψ m, f z = 0 := by
  have hnm : ((n-m:ℤ):ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hmn.symm
  rw [sourceGapFunctional,D.localNumerator_circuit_eq f hf Γ hΓ] at hz
  exact D.localNumerator_zero_of_circle hψ f hf hreal
    ((mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hnm)).resolve_right hw)

/-- The same implication for a numerator given on any open neighborhood
containing the filled original contour disk. -/
theorem SourceCriticalRootPeriodCircle.localNumerator_zero_of_functional_on
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hψ : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (hmn : m ≠ n)
    (f : ℂ → ℂ) (U : Set ℂ) (hf : AnalyticOnNhd ℂ f U)
    (hDU : closedBall (D.center:ℂ) D.radius ⊆ U)
    (hreal : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ m, (f z).im = 0)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m))
    (hw : Γ.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) ≠ 0)
    (hz : sourceGapFunctional hp hp1 n m ψ Γ f = 0) :
    ∃ z ∈ sourcePeriodicSegment hp hp1 ψ m, f z = 0 :=
  D.localNumerator_zero_of_functional hψ n hmn f (hf.mono hDU) hreal Γ hΓ hw hz

end NLS.ZakharovShabat
