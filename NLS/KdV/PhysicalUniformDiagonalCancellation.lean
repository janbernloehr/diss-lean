import NLS.KdV.PhysicalSharpDiagonalCancellation
import NLS.ZakharovShabat.SourceDiagonalCancellationSobolevUniformLittleO

/-! The actual corrected physical diagonal contribution has a uniform
little-o remainder on one fixed full complex native neighborhood. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ} {ht : 0≤t} {J : E →L[ℂ] PeriodOneHminusOne}

theorem PhysicalFrequencyParameterization.exists_uniform_sharp_diagonal_cancellation_decay
    (A : PhysicalFrequencyParameterization E t ht J) (ht0 : 0<t) (ht1 : t<1)
    (q : E) (hq : q ∈ A.domain) (hqr : IsRealPeriodOneHminusOne (J q)) :
    ∃ T : Set E, IsOpen T ∧ q ∈ T ∧ T ⊆ A.domain ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a ∈ T, ∀ n : ℕ+, K ≤ (n:ℤ).natAbs →
        Weight.sobolev (3*t-1) (n:ℤ)*‖A.diagonalRemainder n a‖ ≤ ε := by
  let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
  let φ : realTypeSourceSubmodule 2 := ⟨A.normalizedSource q,A.real_source q hq hqr⟩
  obtain ⟨D,_⟩ := A.physical.atlas.exists_errorDomain
    A.estimates.angular_extension.toSourcePsiNormalizedComplexExtension
    A.physical.psi.family.domain_open A.physical.psi.family.real_subset
  obtain ⟨S,hS,hφS,_,hdiag⟩ := D.exists_local_sobolev_diagonal_cancellation_uniform_littleO
    (sourceHigherActionAtlas (by norm_num) (by norm_num)) A.estimates.angular_extension
    A.physical.psi.family.domain_open A.physical.psi.family.real_subset t ht0 ht1 φ
  obtain ⟨G,hG,hφG,R,hR,hgap⟩ := exists_local_sobolevSquaredGap_bounds t ht (A.normalizedSource q)
  obtain ⟨T,hT,hqT,hTA,hTS,_⟩ := exists_open_common_pullback_domain A.domain A.domain_open q hq
    A.normalizedSource A.analytic_source.continuousOn (S ∩ G) (hS.inter hG) ⟨hφS,hφG⟩
    J J.continuous A.physical.domain A.physical.domain_open (A.domain_subset hq)
  refine ⟨T,hT,hqT,hTA,?_⟩
  intro ε hε
  let δ := ε/(R+1)
  have hδ : 0<δ := div_pos hε (by linarith)
  have hδR : δ*R≤ε := by
    have he : δ*(R+1)=ε := div_mul_cancel₀ ε (by linarith : R+1≠0)
    nlinarith
  obtain ⟨K,hK⟩ := hdiag δ hδ
  refine ⟨K,?_⟩
  intro a ha n hn
  have hreflect : sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
      (L (A.normalizedSource a)) (-(n:ℤ))=
        sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L (A.normalizedSource a)) (n:ℤ) := by
    rw [A.source_identity a (hTA ha)]
    simpa only [sourcePeriodicGapDisplacement_apply] using
      (sourcePeriodicReflection_hillMiuraDiagonal (A.physical.psi.miura.lift (J a))).gap_neg (n:ℤ)
  have hb := hK (A.normalizedSource a) (hTS a ha).1 n hn hreflect
  rw [A.source_identity a (hTA ha)] at hb
  let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
    (hillMiuraDiagonal (A.physical.psi.miura.lift (J a))) (n:ℤ)
  have hd : Weight.sobolev (t-1) (n:ℤ)*‖A.diagonalRemainder n a‖ ≤ ‖γ‖^2*δ := by
    dsimp only [PhysicalFrequencyParameterization.diagonalRemainder,
      PhysicalFrequencyParameterization.renormalizedCorrection]
    rw [A.physical.diagonal_cancellation_identity]
    exact hb
  obtain ⟨g,hgn,hquad,_⟩ := hgap (A.normalizedSource a) (hTS a ha).2
  have hg : ‖g (n:ℤ)‖=Weight.sobolev (2*t) (n:ℤ)*‖γ‖^2 := by
    have h := hquad (n:ℤ)
    rw [A.source_identity a (hTA ha)] at h
    exact h
  have h := Coeff.sobolev_gap_remainder_bound t (n:ℤ) γ (A.diagonalRemainder n a) δ hd
  rw [← hg] at h
  exact h.trans ((mul_le_mul_of_nonneg_left
    ((lp.norm_apply_le_norm (by norm_num : (1:ℝ≥0∞)≠0) g (n:ℤ)).trans hgn) hδ.le).trans hδR)

end NLS.KdV
