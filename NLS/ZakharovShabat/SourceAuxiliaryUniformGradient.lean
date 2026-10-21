import NLS.ZakharovShabat.SourceAuxiliaryUniformAsymptotics
import NLS.SequenceSpaces.SourceConjugateGradient
import NLS.ComplexAnalysis.BanachTaylorBounds

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual corrected auxiliary is scalar analytic on the retained original domain. -/
theorem auxiliary_analytic (H : SourceLemma12_12Data hp hp1 W₀ W s) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceGapWeightedEtaAuxiliary hp hp1 n) W := by
  intro ψ hψ
  have hs := H.dirichlet_omitted_sample_data ψ hψ n
  exact ((analyticAt_const.mul hs.2).inv (mul_ne_zero (by norm_num)
    (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ _ n hs.1))).neg

/-- Cauchy's estimate bounds all actual auxiliary cotangents on one original-source
neighborhood, together with their physical conjugate Fourier gradients. -/
theorem auxiliary_gradient_local_bound (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (hq : q ≠ ⊤) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ U, ∀ n : ℤ,
        ‖fderiv ℂ (sourceGapWeightedEtaAuxiliary hp hp1 n) ψ‖ ≤ C ∧
        ‖CoeffPair.conjugateGradient hp hq
          (fderiv ℂ (sourceGapWeightedEtaAuxiliary hp hp1 n) ψ)‖ ≤ 2*C := by
  obtain ⟨V,hV,hφV,hVW,B,hB,hb⟩ := H.auxiliary_error_local_bound φ hφ
  have hscalar (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
      ‖sourceGapWeightedEtaAuxiliary hp hp1 n ψ‖ ≤ B+1 := by
    have hc := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne'
      (sourceGapWeightedEtaAuxiliaryRemainder hp hp1 ψ) n).trans (hb ψ hψ)
    rw [H.auxiliary_remainder_analytic.2 ψ (hVW hψ) n] at hc
    have hcos : ‖cos ((Real.pi:ℂ)*n)‖ = 1 := by
      rw [cos_freeCenter_eq_natAbs_sign]
      simp
    have ht := norm_sub_le
      (2*sourceGapWeightedEtaAuxiliary hp hp1 n ψ+cos ((Real.pi:ℂ)*n))
      (cos ((Real.pi:ℂ)*n))
    rw [add_sub_cancel_right,norm_mul,hcos] at ht
    norm_num only [norm_ofNat] at ht
    linarith
  obtain ⟨r,hr,hrsub⟩ := Metric.isOpen_iff.mp hV φ hφV
  have hh : 0 < r/2 := by positivity
  refine ⟨ball φ (r/2),isOpen_ball,mem_ball_self hh,
    fun ψ hψ => hVW (hrsub (ball_subset_ball (by linarith) hψ)),
    2*(B+1)/(r/2),by positivity,?_⟩
  intro ψ hψ n
  have hder : ‖fderiv ℂ (sourceGapWeightedEtaAuxiliary hp hp1 n) ψ‖ ≤ 2*(B+1)/(r/2) := by
    apply norm_fderiv_le_of_ball_bound _ φ ψ (r/2) (r/2) (B+1) hh
    · simpa only [show r/2+r/2=r by ring] using
        (H.auxiliary_analytic n).differentiableOn.mono (hrsub.trans hVW)
    · intro χ hχ
      apply hscalar χ (hrsub ?_) n
      simpa only [show r/2+r/2=r by ring] using hχ
    · exact hψ
  exact ⟨hder,(CoeffPair.norm_conjugateGradient_le hp hq _).trans
    (mul_le_mul_of_nonneg_left hder (by norm_num))⟩

/-- The bounded gradient represents the actual full differential through the
physical reversed-frequency pairing. -/
theorem auxiliary_gradient_represents (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (hq : q ≠ ⊤) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) (h : CoeffPair p) :
    HasFDerivAt (sourceGapWeightedEtaAuxiliary hp hp1 n)
      (fderiv ℂ (sourceGapWeightedEtaAuxiliary hp hp1 n) ψ) ψ ∧
    let g := CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (sourceGapWeightedEtaAuxiliary hp hp1 n) ψ)
    Coeff.dualPairing (Coeff.reflection g.fst) h.fst+
      Coeff.dualPairing (Coeff.reflection g.snd) h.snd =
        fderiv ℂ (sourceGapWeightedEtaAuxiliary hp hp1 n) ψ h := by
  exact ⟨(H.auxiliary_analytic n ψ hψ).differentiableAt.hasFDerivAt,
    CoeffPair.dualPairing_conjugateGradient hp hq _ h⟩

end SourceLemma12_12Data
end NLS.ZakharovShabat
