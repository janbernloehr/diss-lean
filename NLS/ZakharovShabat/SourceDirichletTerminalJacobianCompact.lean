import NLS.ZakharovShabat.SourceDirichletTerminalDifferential
import NLS.ZakharovShabat.SourceGapWeightedEtaClosedSummability
import NLS.ZakharovShabat.SourceSection20SobolevDomain
import NLS.ZakharovShabat.SourceLemmaG7
import NLS.SequenceSpaces.CompactRowMajorant
import NLS.SequenceSpaces.PairExponentIdentity

/-! The actual literal terminal derivative is a compact perturbation of
its exact signed Fourier map. All complex sources on one neighborhood
of the entire real Hilbert locus are covered, including open gaps.
The dense approximation uses ordinary H¹ sources in the L² norm. -/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact signed free terminal Fourier operator. -/
def sourceGapWeightedEtaTerminalFourier (sign : ℂ) : CoeffPair p →L[ℂ] Coeff p :=
  (sign-1) • (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).comp (CoeffPair.toMax p).toContinuousLinearMap))-
  (sign+1) • ((ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).comp
    (CoeffPair.toMax p).toContinuousLinearMap)

@[simp] theorem sourceGapWeightedEtaTerminalFourier_apply (sign : ℂ) (h : CoeffPair p) (n : ℤ) :
    sourceGapWeightedEtaTerminalFourier sign h n = (sign-1)*h.fst (-n)-(sign+1)*h.snd n := rfl

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The inverse-product error is summable at every original complex source,
with the exact free parity retained. -/
theorem memlp_dirichlet_omitted_inverse_sub_free (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    Memℓp (fun n : ℤ => (sourceStandardRootOmittedProduct hp hp1 n φ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n))⁻¹-
        cos ((Real.pi : ℂ)*n)) p := by
  have hm := lp.memℓp (Coeff.multiplierCLM sourceDirichletParitySymbol
    (sourceDirichletOmittedInverseError hp hp1 φ))
  convert hm using 1
  funext n
  have he := H.dirichlet_omitted_inverse_symbol_apply φ hφ n
  change (-1 : ℂ)^n.natAbs*(1+sourceDirichletOmittedInverseError hp hp1 φ n) = _ at he
  change _ = (-1 : ℂ)^n.natAbs*sourceDirichletOmittedInverseError hp hp1 φ n
  rw [← he,cos_freeCenter_eq_natAbs_sign]
  ring

/-- The G.6/G.7 estimates imply the closed expression estimate at complex
sources too: the actual analytic inverse sequence replaces a real-source bound. -/
theorem memlp_terminal_closed_sub_free_of_gradient_estimates
    (H : SourceLemma12_12Data hp hp1 W₀ W s) (φ : CoeffPair p) (hφ : φ ∈ W)
    (hmid : Memℓp (fun n : ℤ => fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ) p)
    (hdir : Memℓp (fun n : ℤ => fderiv ℂ (fun ψ : CoeffPair p =>
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) φ-sourceFreeDirichletCotangent p n) p)
    (hanti : Memℓp (fun n : ℤ => sourceAntiDiscriminantCotangent hp hp1
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n) φ-
      sourceAntiDiscriminantCotangent hp hp1 ((Real.pi : ℂ)*n) 0) p) (sign : ℂ) :
    Memℓp (fun n : ℤ => sourceGapWeightedEtaClosedCotangent hp hp1 n sign φ-
      sourceGapWeightedEtaFreeCotangent hp hp1 n sign) p := by
  let μ (n : ℤ) := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
  let dμ (n : ℤ) := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) φ
  let dτ (n : ℤ) := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ
  let A (n : ℤ) := sourceAntiDiscriminantCotangent hp hp1 (μ n) φ
  let A₀ (n : ℤ) := sourceAntiDiscriminantCotangent hp hp1 ((Real.pi : ℂ)*n) 0
  let B (n : ℤ) := (sourceStandardRootOmittedProduct hp hp1 n φ (μ n))⁻¹
  let δ (n : ℤ) := deriv (sourceAntiDiscriminantCandidate hp hp1 φ) (μ n)
  change Memℓp dτ p at hmid
  change Memℓp (fun n => dμ n-sourceFreeDirichletCotangent p n) p at hdir
  change Memℓp (fun n => A n-A₀ n) p at hanti
  have hinv : Memℓp (fun n => B n-cos ((Real.pi : ℂ)*n)) p :=
    H.memlp_dirichlet_omitted_inverse_sub_free φ hφ
  have hδ : Memℓp δ p := (memℓp_sourceAntiDiscriminant_at_dirichletRoots hp hp1 φ).2
  have hC (n : ℤ) : ‖B n‖ ≤ ‖sourceDirichletOmittedInverseSymbol hp hp1 φ‖ := by
    dsimp only [B,μ]
    rw [← H.dirichlet_omitted_inverse_symbol_apply φ hφ n]
    exact lp.norm_apply_le_norm (by simp) _ n
  obtain ⟨M,_,hM⟩ := exists_norm_bound_of_memlp hdir
  have hdμ (n : ℤ) : ‖dμ n‖ ≤ M+1 := by
    calc
      ‖dμ n‖ = ‖(dμ n-sourceFreeDirichletCotangent p n)+sourceFreeDirichletCotangent p n‖ := by rw [sub_add_cancel]
      _ ≤ ‖dμ n-sourceFreeDirichletCotangent p n‖+‖sourceFreeDirichletCotangent p n‖ := norm_add_le _ _
      _ ≤ M+1 := add_le_add (hM n) (norm_sourceFreeDirichletCotangent_le n)
  have h₁ := memlp_smul_of_bounded_scalar B _ hanti _ hC
  have h₂ := memlp_smul_of_bounded_vector _ A₀ hinv 2 (norm_sourceAntiDiscriminantCotangent_zero_le hp hp1)
  have h₃ := memlp_smul_of_bounded_scalar B _
    (memlp_smul_of_bounded_vector δ dμ hδ (M+1) hdμ) _ hC
  have hsum := ((hdir.const_smul (-2 : ℂ)).add (hmid.const_smul (2 : ℂ))).sub
    (((h₁.add h₂).add h₃).const_smul (sign*I))
  convert hsum using 1
  funext n
  exact sourceGapWeightedEtaClosedCotangent_sub_free hp hp1 φ n sign

end SourceLemma12_12Data

/-- A single common complex domain supports the actual terminal/Fourier
compact derivative remainder for every sign and every source there. -/
theorem exists_gapWeightedEtaTerminalSequence_compact_derivative_domain :
    ∃ W : Set (CoeffPair 2), IsOpen W ∧ realTypeSourceLocus 2 ⊆ W ∧
      ∀ sign : ℂ, AnalyticOnNhd ℂ
        (sourceGapWeightedEtaTerminalSequence (by simp) (by norm_num) sign) W ∧
      ∀ φ ∈ W,
        (∀ n, sourceGapWeightedEtaTerminalSequence (by simp) (by norm_num) sign φ n =
          sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) n sign φ) ∧
        IsCompactOperator (fderiv ℂ
          (sourceGapWeightedEtaTerminalSequence (by simp) (by norm_num) sign) φ-
            sourceGapWeightedEtaTerminalFourier (p := 2) sign) := by
  obtain ⟨W₀,_,_,_,V,hV,_,hrealV,s,H⟩ := sourceLemma12_12 (p := 2) (by simp) (by norm_num)
  obtain ⟨G,hG,hrealG,hgrad⟩ := exists_global_source_spectral_gradients_sobolev_memlp
    (p := 2) (by simp) (by norm_num) le_rfl
  let W := V ∩ G
  have hW : IsOpen W := hV.inter hG
  refine ⟨W,hW,fun φ hφ => ⟨hrealV hφ,hrealG hφ⟩,?_⟩
  intro sign
  let T := sourceGapWeightedEtaTerminalSequence (p := 2) (by simp) (by norm_num) sign
  let F := sourceGapWeightedEtaTerminalFourier (p := 2) sign
  have hT : AnalyticOnNhd ℂ T V := H.gapWeightedEtaTerminalSequence_analytic sign
  refine ⟨hT.mono inter_subset_left,fun φ hφ => ⟨?_,?_⟩⟩
  · intro n
    exact H.gapWeightedEtaTerminalSequence_apply φ hφ.1 n sign
  · have hsmooth (a : ScalarDomain 2 × ScalarDomain 2) (ha : sobolevSourceInclusion a ∈ W) :
        IsCompactOperator (fderiv ℂ T (sobolevSourceInclusion a)-F) := by
      let ψ := sobolevSourceInclusion a
      have hg := hgrad ψ (by simpa only [CoeffPair.exponentInclusion_refl] using ha.2)
        (sourceG3ClassicalCoefficients a) (sourceG7_periodic_representative a)
      simp only [CoeffPair.exponentInclusion_refl] at hg
      have hanti := memlp_source_antiDiscriminantCotangent_boundary_error
        (p := 2) (by simp) (by norm_num) le_rfl ψ (sourceG3ClassicalCoefficients a)
        (sourceG7_periodic_representative a) .dirichlet
      simp only [CoeffPair.exponentInclusion_refl] at hanti
      have hclosed := H.memlp_terminal_closed_sub_free_of_gradient_estimates ψ ha.1 hg.1 hg.2 hanti sign
      have hfull := (H.memlp_gapWeightedEtaTerminalCoordinate_fderiv_sub_closed ψ ha.1 sign).add hclosed
      let L (n : ℤ) := fderiv ℂ (sourceGapWeightedEtaTerminalCoordinate (p := 2)
        (by simp) (by norm_num) n sign) ψ-sourceGapWeightedEtaFreeCotangent (by simp) (by norm_num) n sign
      have hL : Memℓp L 2 := by
        convert hfull using 1
        funext n
        exact (sub_add_sub_cancel _ _ _).symm
      let b : Coeff 2 := ⟨fun n => (‖L n‖ : ℂ),Memℓp.of_norm (by
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_norm] using hL.norm)⟩
      apply Coeff.isCompactOperator_of_rowMajorant (by simp) _ b
      intro n h
      change ‖(fderiv ℂ T ψ) h n-F h n‖ ≤ ‖(‖L n‖ : ℂ)‖*‖h‖
      rw [H.gapWeightedEtaTerminalSequence_fderiv_apply ψ h ha.1 n sign,
        sourceGapWeightedEtaTerminalFourier_apply,
        ← sourceGapWeightedEtaFreeCotangent_apply (by simp) (by norm_num) n sign h]
      simpa only [L,sub_apply,Complex.norm_real,Real.norm_eq_abs,abs_norm] using (L n).le_opNorm h
    obtain ⟨a,ha,hat⟩ := mem_closure_iff_seq_limit.mp (sobolevSourceInclusion_denseRange φ)
    have hev : ∀ᶠ k in atTop, a k ∈ W := hat.eventually (hW.mem_nhds hφ)
    have hc : ContinuousAt (fun ψ => fderiv ℂ T ψ-F) φ :=
      ((hT φ hφ.1).contDiffAt.continuousAt_fderiv (n := 1) one_ne_zero).sub continuousAt_const
    have hcompact : ∀ᶠ k in atTop, IsCompactOperator (fderiv ℂ T (a k)-F) := by
      filter_upwards [hev] with k hk
      obtain ⟨b,hb⟩ := ha k
      rw [← hb] at hk ⊢
      exact hsmooth b hk
    exact isClosed_setOfPred_isCompactOperator.mem_of_tendsto (hc.tendsto.comp hat) hcompact

end NLS.ZakharovShabat
