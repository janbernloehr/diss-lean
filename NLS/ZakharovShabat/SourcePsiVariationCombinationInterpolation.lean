import NLS.ZakharovShabat.SourcePsiInterpolationQuotientExterior
import NLS.ZakharovShabat.SourcePsiLimitOperatorContour
import NLS.ZakharovShabat.CentralCircleThresholds

/-! # Interpolation uniqueness for combinations of deleted psi variations

The proved restored-factor estimate also controls each bare psi variation
on large circles, where the restored linear factor has norm at least one.
Two different deleted indices can therefore be combined over one full
gap-zero product. An entire combination with a zero in every real gap
vanishes by the filled-quotient maximum-modulus argument.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual bare deleted-root variation divided by any full `ℓp`
root product tends uniformly to zero on expanding central circles. -/
theorem eventually_centralCircle_sourcePsiCandidateVariation_quotient_small
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun k => ρ k-(Real.pi:ℂ)*k) p)
    (n : ℤ) (a h : Coeff p) (hdeleted : h n = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      entireSingleSpectralProduct ρ z ≠ 0 ∧
      ‖sourcePsiCandidateVariation n a h z / entireSingleSpectralProduct ρ z‖ ≤ ε := by
  obtain ⟨K,hK⟩ := eventually_centralCircle_sourcePsi_interpolationQuotient_small hp hp1 ρ hρlp n a h hdeleted hε
  filter_upwards [eventually_ge_atTop K,
    tendsto_centralCircleRadius_atTop.eventually_ge_atTop (‖displacedRoots a n‖+1)] with k hk hlarge z hz
  obtain ⟨hG,hbound⟩ := hK k hk z hz
  have hnorm : ‖z‖ = centralCircleRadius k := by simpa only [mem_sphere,dist_zero_right] using hz
  have hfactor : 1 ≤ ‖displacedRoots a n-z‖ := by
    have htriangle := norm_sub_norm_le z (displacedRoots a n)
    rw [norm_sub_rev] at htriangle
    rw [hnorm] at htriangle
    linarith
  have he : ‖((displacedRoots a n-z)*sourcePsiCandidateVariation n a h z)/
      entireSingleSpectralProduct ρ z‖ =
      ‖displacedRoots a n-z‖*‖sourcePsiCandidateVariation n a h z/entireSingleSpectralProduct ρ z‖ := by
    rw [mul_div_assoc,norm_mul]
  rw [he] at hbound
  exact ⟨hG,(le_mul_of_one_le_left (norm_nonneg _) hfactor).trans hbound⟩

/-- The difference of two entire deleted-root variations, even at
different deleted indices, has the same uniform quotient decay. -/
theorem eventually_centralCircle_sourcePsiCandidateVariation_sub_quotient_small
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun k => ρ k-(Real.pi:ℂ)*k) p)
    (n m : ℤ) (a h b v : Coeff p) (hn : h n = 0) (hm : v m = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ‖(sourcePsiCandidateVariation n a h z-sourcePsiCandidateVariation m b v z)/
        entireSingleSpectralProduct ρ z‖ ≤ ε := by
  filter_upwards [eventually_centralCircle_sourcePsiCandidateVariation_quotient_small hp hp1 ρ hρlp n a h hn
      (by positivity : 0 < ε/2),
    eventually_centralCircle_sourcePsiCandidateVariation_quotient_small hp hp1 ρ hρlp m b v hm
      (by positivity : 0 < ε/2)] with k hkn hkm z hz
  rw [sub_div]
  exact (norm_sub_le _ _).trans (by linarith [(hkn z hz).2,(hkm z hz).2])

/-- A full gap-zero sequence and uniform quotient decay force an
entire numerator to vanish. Its simple comparison product is derived
from the actual real gap placement. -/
theorem sourceEntireNumerator_eq_zero_of_gapZero_sequence
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F univ)
    (ρ : ℤ → ℂ) (hρlp : Memℓp (fun k => ρ k-(Real.pi:ℂ)*k) p)
    (hρ : ∀ k : ℤ, ρ k ∈ sourcePeriodicSegment hp hp1 φ.val k)
    (hzero : ∀ k : ℤ, F (ρ k) = 0)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k), ‖F z/entireSingleSpectralProduct ρ z‖ ≤ ε) :
    F = 0 := by
  let b : Coeff p := ⟨fun k => ρ k-(Real.pi:ℂ)*k,hρlp⟩
  have hroot (k : ℤ) : displacedRoots b k = ρ k := by dsimp [b,displacedRoots]; ring
  have hb : b ∈ sourcePeriodicGapRootSet hp hp1 φ.val := by
    intro k
    rw [hroot]
    exact hρ k
  have hρinj : Function.Injective ρ := by
    have hsep := displacedRoots_injective_of_periodicGapRootSet hp hp1 b φ.val φ.property hb
    intro i j hij
    apply hsep
    rwa [hroot i,hroot j]
  have hsimple := entireSingleSpectralProduct_simple_zeros_of_injective hp hp1 ρ hρlp hρinj
  have hcommon : ∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 → F z = 0 := by
    intro z hz
    obtain ⟨k,hk⟩ := (entireSingleSpectralProduct_eq_zero_iff_of_lp hp ρ hρlp z).mp hz
    rw [← hk]
    exact hzero k
  obtain ⟨K,hK⟩ := eventually_centralCircle_entireSingleSpectralProduct_ne_zero hp ρ hρlp
  let R : ℕ → ℝ := fun j => centralCircleRadius (j+K)
  apply NLS.ComplexAnalysis.entire_eq_zero_of_simple_zero_interpolation hF
    (analyticOnNhd_entireSingleSpectralProduct hp ρ hρlp) hcommon hsimple R
    (tendsto_centralCircleRadius_atTop.comp (tendsto_add_atTop_nat K))
    (fun j z hz => hK (j+K) (by omega) z hz)
  intro ε hε
  have he := (tendsto_add_atTop_nat K).eventually (hdecay ε hε)
  exact he

/-- A difference of actual entire root variations with one zero in
every real gap vanishes, without an assumed growth estimate. -/
theorem sourcePsiCandidateVariation_sub_eq_zero_of_gapZero_sequence
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (ρ : ℤ → ℂ) (hρlp : Memℓp (fun k => ρ k-(Real.pi:ℂ)*k) p)
    (hρ : ∀ k : ℤ, ρ k ∈ sourcePeriodicSegment hp hp1 φ.val k)
    (n m : ℤ) (a h b v : Coeff p) (hn : h n = 0) (hm : v m = 0)
    (hzero : ∀ k : ℤ, sourcePsiCandidateVariation n a h (ρ k)-sourcePsiCandidateVariation m b v (ρ k) = 0) :
    (fun z => sourcePsiCandidateVariation n a h z-sourcePsiCandidateVariation m b v z) = 0 :=
  sourceEntireNumerator_eq_zero_of_gapZero_sequence hp hp1 φ _
    ((analyticOnNhd_sourcePsiCandidateVariation hp hp1 n a h).sub
      (analyticOnNhd_sourcePsiCandidateVariation hp hp1 m b v)) ρ hρlp hρ hzero
    (fun _ hε => eventually_centralCircle_sourcePsiCandidateVariation_sub_quotient_small
      hp hp1 ρ hρlp n m a h b v hn hm hε)

end NLS.ZakharovShabat
