import NLS.ZakharovShabat.SourcePsiVariationCombinationInterpolation
import NLS.ZakharovShabat.BalancedSingleSpectralProducts

/-! Interpolation uniqueness for odd parts of deleted-root psi
variations. A balanced full comparison product controls both z and
-z on the same expanding circles and with the same gap-zero labels. -/
noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem eventually_centralCircle_odd_psiVariation_sub_quotient_small
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun k => ρ k-(Real.pi:ℂ)*k) p)
    (hρ0 : ρ 0=0) (hρneg : ∀ j : ℤ, ρ (-j) = -ρ j)
    (n m : ℤ) (a h b v : Coeff p) (hn : h n=0) (hm : v m=0)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ‖((sourcePsiCandidateVariation n a h z-sourcePsiCandidateVariation n a h (-z))-
        (sourcePsiCandidateVariation m b v z-sourcePsiCandidateVariation m b v (-z)))/
        entireSingleSpectralProduct ρ z‖ ≤ ε := by
  filter_upwards [eventually_centralCircle_sourcePsiCandidateVariation_quotient_small hp hp1 ρ hρlp
      n a h hn (by positivity : 0<ε/4),
    eventually_centralCircle_sourcePsiCandidateVariation_quotient_small hp hp1 ρ hρlp
      m b v hm (by positivity : 0<ε/4)] with k hkn hkm z hz
  have hnz : -z ∈ sphere (0:ℂ) (centralCircleRadius k) := by
    simpa only [mem_sphere,dist_zero_right,norm_neg] using hz
  have hG : entireSingleSpectralProduct ρ (-z) = -entireSingleSpectralProduct ρ z :=
    entireSingleSpectralProduct_neg_of_balanced hp ρ hρlp hρ0 hρneg z
  have hAn := (hkn (-z) hnz).2
  have hBn := (hkm (-z) hnz).2
  rw [hG,div_neg,norm_neg] at hAn hBn
  rw [sub_div,sub_div,sub_div]
  apply (norm_sub_le _ _).trans
  have hA := norm_sub_le (sourcePsiCandidateVariation n a h z/entireSingleSpectralProduct ρ z)
    (sourcePsiCandidateVariation n a h (-z)/entireSingleSpectralProduct ρ z)
  have hB := norm_sub_le (sourcePsiCandidateVariation m b v z/entireSingleSpectralProduct ρ z)
    (sourcePsiCandidateVariation m b v (-z)/entireSingleSpectralProduct ρ z)
  linarith [(hkn z hz).2,(hkm z hz).2]

theorem source_oddPsiVariation_sub_eq_zero_of_balanced_gapZero_sequence
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (ρ : ℤ → ℂ) (hρlp : Memℓp (fun k => ρ k-(Real.pi:ℂ)*k) p)
    (hρ0 : ρ 0=0) (hρneg : ∀ j : ℤ, ρ (-j) = -ρ j)
    (hρ : ∀ j : ℤ, ρ j ∈ sourcePeriodicSegment hp hp1 φ.val j)
    (n m : ℤ) (a h b v : Coeff p) (hn : h n=0) (hm : v m=0)
    (hzero : ∀ j : ℤ,
      (sourcePsiCandidateVariation n a h (ρ j)-sourcePsiCandidateVariation n a h (-ρ j))-
        (sourcePsiCandidateVariation m b v (ρ j)-sourcePsiCandidateVariation m b v (-ρ j))=0) :
    (fun z : ℂ => (sourcePsiCandidateVariation n a h z-sourcePsiCandidateVariation n a h (-z))-
      (sourcePsiCandidateVariation m b v z-sourcePsiCandidateVariation m b v (-z))) = 0 := by
  have hA := analyticOnNhd_sourcePsiCandidateVariation hp hp1 n a h
  have hB := analyticOnNhd_sourcePsiCandidateVariation hp hp1 m b v
  apply sourceEntireNumerator_eq_zero_of_gapZero_sequence hp hp1 φ _
    (show AnalyticOnNhd ℂ _ univ from fun z _ =>
      ((hA z (mem_univ _)).sub ((hA (-z) (mem_univ _)).comp
        (f := fun w : ℂ => -w) analyticAt_id.neg)).sub
      ((hB z (mem_univ _)).sub ((hB (-z) (mem_univ _)).comp
        (f := fun w : ℂ => -w) analyticAt_id.neg)))
    ρ hρlp hρ hzero
  intro ε hε
  exact eventually_centralCircle_odd_psiVariation_sub_quotient_small hp hp1 ρ hρlp hρ0 hρneg
    n m a h b v hn hm hε

end NLS.ZakharovShabat
