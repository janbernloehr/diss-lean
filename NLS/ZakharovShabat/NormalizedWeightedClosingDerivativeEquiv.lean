import NLS.ZakharovShabat.NormalizedWeightedClosingCompatibility
import NLS.ComplexAnalysis.NearIdentityAnalyticInverse

/-! # Compatible inverses of actual adapted derivatives

Near-identity estimates construct the weighted and unweighted derivative
equivalences, each with inverse norm at most two. Differentiating the
actual decoding identity proves compatibility of both derivatives and
their bounded inverses at every complex source and every late cutoff.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem derivative_intertwines_of_germ
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (J : E →L[ℂ] F) (A : E → E) (B : F → F) (a : E)
    (hA : AnalyticAt ℂ A a) (hB : AnalyticAt ℂ B (J a))
    (h : (fun x => J (A x)) =ᶠ[𝓝 a] fun x => B (J x)) :
    J.comp (fderiv ℂ A a) = (fderiv ℂ B (J a)).comp J := by
  have hl := J.hasFDerivAt.comp a hA.differentiableAt.hasFDerivAt
  have hr := hB.differentiableAt.hasFDerivAt.comp a J.hasFDerivAt
  exact (hl.congr_of_eventuallyEq h.symm).unique hr

private theorem inverse_intertwines
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (J : E →L[ℂ] F) (A : E ≃L[ℂ] E) (B : F ≃L[ℂ] F)
    (h : J.comp A.toContinuousLinearMap = B.toContinuousLinearMap.comp J) :
    J.comp A.symm.toContinuousLinearMap = B.symm.toContinuousLinearMap.comp J := by
  apply ContinuousLinearMap.ext
  intro x
  apply B.injective
  have hx := congrArg (fun L => L (A.symm x)) h
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using hx.symm

/-- Both actual derivatives are constructed equivalences and their inverses commute with decoding. -/
theorem exists_uniform_normalizedWeightedClosingMap_derivative_equivs
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      AnalyticAt ℂ (fun ψ => normalizedWeightedClosingMap hp w ψ N) φ ∧
      AnalyticAt ℂ (fun ψ => sourceAdaptedClosingMap hp ψ N) (normalizedWeightedSource w φ) ∧
      ∃ A B : CoeffPair p ≃L[ℂ] CoeffPair p,
        A.toContinuousLinearMap = fderiv ℂ (fun ψ => normalizedWeightedClosingMap hp w ψ N) φ ∧
        B.toContinuousLinearMap = fderiv ℂ (fun ψ => sourceAdaptedClosingMap hp ψ N) (normalizedWeightedSource w φ) ∧
        ‖A.symm.toContinuousLinearMap‖ ≤ 2 ∧ ‖B.symm.toContinuousLinearMap‖ ≤ 2 ∧
        (normalizedWeightedSourceCLM w).comp A.toContinuousLinearMap =
          B.toContinuousLinearMap.comp (normalizedWeightedSourceCLM w) ∧
        (normalizedWeightedSourceCLM w).comp A.symm.toContinuousLinearMap =
          B.symm.toContinuousLinearMap.comp (normalizedWeightedSourceCLM w) := by
  obtain ⟨Nc,hNc,U,hoU,hφU,hC⟩ := exists_uniform_normalizedWeightedClosingMap_decode hp hp1 w φ
  obtain ⟨rw,hrw,Nw,_,hw⟩ := exists_fixedBall_normalizedWeightedClosingMap_derivative hp hp1 w φ (1/2) (by norm_num)
  obtain ⟨ru,hru,Nu,_,hu⟩ := exists_fixedBall_sourceAdaptedClosingMap_derivative hp hp1
    (normalizedWeightedSource w φ) (1/2) (by norm_num)
  refine ⟨max Nc (max Nw Nu),by omega,fun N hN => ?_⟩
  have hwN := hw N (by omega)
  have huN := hu N (by omega)
  have hAw := hwN.1 φ (mem_ball_self (by positivity))
  have hAu := huN.1 (normalizedWeightedSource w φ) (mem_ball_self (by positivity))
  obtain ⟨A,hA,hAb⟩ := NLS.ComplexAnalysis.exists_continuousLinearEquiv_of_norm_sub_id_le_half
    (fderiv ℂ (fun ψ => normalizedWeightedClosingMap hp w ψ N) φ)
    (hwN.2.2.1 φ (mem_ball_self (by positivity))).le
  obtain ⟨B,hB,hBb⟩ := NLS.ComplexAnalysis.exists_continuousLinearEquiv_of_norm_sub_id_le_half
    (fderiv ℂ (fun ψ => sourceAdaptedClosingMap hp ψ N) (normalizedWeightedSource w φ))
    (huN.2.2.1 (normalizedWeightedSource w φ) (mem_ball_self (by positivity))).le
  have hc : (normalizedWeightedSourceCLM w).comp A.toContinuousLinearMap =
      B.toContinuousLinearMap.comp (normalizedWeightedSourceCLM w) := by
    rw [hA,hB]
    apply derivative_intertwines_of_germ (normalizedWeightedSourceCLM w)
      (fun ψ => normalizedWeightedClosingMap hp w ψ N) (fun ψ => sourceAdaptedClosingMap hp ψ N) φ hAw hAu
    filter_upwards [hoU.mem_nhds hφU] with ψ hψ
    exact hC N (by omega) ψ hψ
  exact ⟨hAw,hAu,A,B,hA,hB,hAb,hBb,hc,inverse_intertwines _ _ _ hc⟩
end NLS.ZakharovShabat
