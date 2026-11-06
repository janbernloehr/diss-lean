import NLS.ZakharovShabat.SourceRealGapCoefficientContinuity
import NLS.ZakharovShabat.SourceDiagonalPositiveGaps
import NLS.ZakharovShabat.SourceDiagonalLaurentAtlas
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Inverse-frequency actions under bounded Fourier limits

Every positive real diagonal gap is strictly separated from zero. The
inverse-frequency real cosine integrand therefore converges uniformly
under bounded coefficient limits, including collapsed gaps. Integrating
its actual arcosh profile proves continuity of the Laurent level-zero
action without assuming strong source convergence.
-/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem tendsto_sourceInverseFrequencyGapProfile_of_bounded_coefficientwise
    {A : Type*} {l : Filter A} (φ : A → CoeffPair 2) (ψ : CoeffPair 2)
    (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax 2 (φ k))) (hψ : IsRealType (CoeffPair.toMax 2 ψ))
    (hdiag : ψ.fst = ψ.snd)
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (n : ℤ) (hn : 0 < n) (θ : A → ℝ) (t : ℝ) (hθ : Tendsto θ l (𝓝 t)) :
    Tendsto (fun k => (realGapAffinePoint (by simp) (by norm_num) (φ k) n (Real.cos (θ k)))⁻¹ *
      (Real.sin (θ k)*sourceRealGapCosineProfile (by simp) (by norm_num) (φ k) n (θ k))) l
      (𝓝 ((realGapAffinePoint (by simp) (by norm_num) ψ n (Real.cos t))⁻¹ *
        (Real.sin t*sourceRealGapCosineProfile (by simp) (by norm_num) ψ n t))) := by
  have hx := tendsto_realGapAffinePoint_cos_of_bounded_coefficientwise φ ψ hb hφ hψ ht n θ t hθ
  have hp := tendsto_sourceRealGapCosineProfile_of_bounded_coefficientwise φ ψ hb hφ hψ ht n θ t hθ
  exact (hx.inv₀ (ne_of_gt (sourceDiagonal_positive_gapAffinePoint_cos
    (by simp) (by norm_num) ⟨ψ,hψ⟩ hdiag n hn t))).mul
      ((Real.continuous_sin.continuousAt.tendsto.comp hθ).mul hp)

theorem tendsto_sourceRealLaurentAction_zero_of_bounded_coefficientwise
    {A : Type*} {l : Filter A} [l.IsCountablyGenerated]
    (φ : A → CoeffPair 2) (ψ : CoeffPair 2) (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax 2 (φ k))) (hψ : IsRealType (CoeffPair.toMax 2 ψ))
    (hdiagφ : ∀ k, (φ k).fst = (φ k).snd) (hdiagψ : ψ.fst = ψ.snd)
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (n : ℤ) (hn : 0 < n) :
    Tendsto (fun k => sourceRealLaurentAction (by simp) (by norm_num) ⟨φ k,hφ k⟩ n 0) l
      (𝓝 (sourceRealLaurentAction (by simp) (by norm_num) ⟨ψ,hψ⟩ n 0)) := by
  let F : A → ℝ → ℝ := fun k θ =>
    (realGapAffinePoint (by simp) (by norm_num) (φ k) n (Real.cos θ))⁻¹ *
      (Real.sin θ*sourceRealGapCosineProfile (by simp) (by norm_num) (φ k) n θ)
  let f : ℝ → ℝ := fun θ =>
    (realGapAffinePoint (by simp) (by norm_num) ψ n (Real.cos θ))⁻¹ *
      (Real.sin θ*sourceRealGapCosineProfile (by simp) (by norm_num) ψ n θ)
  have hF : TendstoUniformlyOn F f l (Icc 0 Real.pi) := by
    apply NLS.ComplexAnalysis.tendstoUniformlyOn_of_joint_limits isCompact_Icc
      (continuous_sourceInverseFrequencyGapProfile (by simp) (by norm_num) ⟨ψ,hψ⟩ hdiagψ n hn).continuousOn
    intro t _
    exact tendsto_sourceInverseFrequencyGapProfile_of_bounded_coefficientwise
      (fun q : A × ℝ => φ q.1) ψ (hb.subset (range_comp_subset_range Prod.fst φ))
      (fun q => hφ q.1) hψ hdiagψ (fun j => (ht j).comp tendsto_fst) n hn Prod.snd t
      (tendsto_snd.mono_right nhdsWithin_le_nhds)
  have hcont : ∀ᶠ k in l, ContinuousOn (F k) (Set.uIcc (0 : ℝ) Real.pi) :=
    Eventually.of_forall fun k => (continuous_sourceInverseFrequencyGapProfile (by simp) (by norm_num)
      ⟨φ k,hφ k⟩ (hdiagφ k) n hn).continuousOn
  have hI := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn (μ := MeasureTheory.volume) hcont
    (by simpa only [Set.uIcc_of_le Real.pi_pos.le] using hF)
  have he := tendsto_source_canonicalPeriodicMidpoint_and_gap_of_bounded_coefficientwise
    (by simp) (by norm_num) φ ψ hb hφ hψ ht n
  have h := ((continuous_re.continuousAt.tendsto.comp he.2).div_const Real.pi).mul hI
  have hc := continuous_ofReal.continuousAt.tendsto.comp h
  simpa only [sourceRealLaurentAction,show (0 : ℤ)-1 = -1 by norm_num,zpow_neg_one,F,f,Function.comp_def] using! hc

theorem tendsto_sourceDiagonalLaurentAction_zero_of_bounded_coefficientwise
    {A : Type*} {l : Filter A} [l.IsCountablyGenerated]
    (φ : A → CoeffPair 2) (ψ : CoeffPair 2) (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, φ k ∈ realDiagonalSourceLocus 2) (hψ : ψ ∈ realDiagonalSourceLocus 2)
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (n : ℤ) (hn : 0 < n) :
    Tendsto (fun k => sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (φ k)) l
      (𝓝 (sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 ψ)) := by
  have he (χ : realDiagonalSourceLocus 2) := sourceDiagonalLaurentAction_eq_real (by simp) (by norm_num)
    ⟨χ.val,χ.property.1⟩ (realDiagonal_subset_sourceDiagonalLaurentDomain (by simp) (by norm_num) χ.property) n 0 (ne_of_gt hn)
  have h := tendsto_sourceRealLaurentAction_zero_of_bounded_coefficientwise φ ψ hb
    (fun k => (hφ k).1) hψ.1 (fun k => (hφ k).2) hψ.2 ht n hn
  simpa only [← he ⟨ψ,hψ⟩,← he ⟨φ _,hφ _⟩] using h

end NLS.ZakharovShabat
