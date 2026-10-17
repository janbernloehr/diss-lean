import NLS.ZakharovShabat.NormalizedWeightedClosingDerivative
import NLS.ZakharovShabat.SourceAdaptedClosingMap
import NLS.ZakharovShabat.SourceSymmetricTruncate

/-! # Compact derivative remainders of the adapted maps

Differences between two cutoffs have finite output support. Differentiating
that identity approximates the fixed derivative minus the identity by
compact operators. Uniform derivative estimates make the remaining error
arbitrarily small. The result holds at complex sources for every spectral
weight and specializes to the original unit-weight adapted map.
-/

noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem cutoff_scalar_difference (N M : ℕ) (hNM : N ≤ M+1) (n : ℤ)
    (a z x y : ℂ)
    (hx : x = if N ≤ n.natAbs then z else a)
    (hy : y = if M+1 ≤ n.natAbs then z else a) :
    x-y = if n ∈ Finset.Icc (-(M:ℤ)) M then x-a else 0 := by
  by_cases hn : n ∈ Finset.Icc (-(M:ℤ)) M
  · have hm : ¬M+1 ≤ n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
    rw [if_pos hn,hy,if_neg hm]
  · have hm : M+1 ≤ n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
    rw [if_neg hn,hx,hy,if_pos (hNM.trans hm),if_pos hm,sub_self]

/-- Exact finite-output difference between two actual adapted cutoffs. -/
theorem normalizedWeightedClosingMap_cutoff_difference
    (hp : p ≠ ⊤) (w : SpectralWeight) (ψ : CoeffPair p) (N M : ℕ) (hNM : N ≤ M+1)
    (hN : ∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp w
      (normalizedWeightedPeriodOne w ψ) N positive) p)
    (hM : ∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp w
      (normalizedWeightedPeriodOne w ψ) (M+1) positive) p) :
    normalizedWeightedClosingMap hp w ψ N-normalizedWeightedClosingMap hp w ψ (M+1) =
      sourceSymmetricTruncateCLM M (normalizedWeightedClosingMap hp w ψ N-ψ) := by
  have hn := normalizedWeightedClosingMap_apply_of_mem hp w ψ N hN
  have hm := normalizedWeightedClosingMap_apply_of_mem hp w ψ (M+1) hM
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext n
  · change (normalizedWeightedClosingMap hp w ψ N).fst n-
        (normalizedWeightedClosingMap hp w ψ (M+1)).fst n =
      Coeff.truncate (Finset.Icc (-(M:ℤ)) M) (normalizedWeightedClosingMap hp w ψ N-ψ).fst n
    rw [Coeff.truncate_apply]
    exact cutoff_scalar_difference N M hNM n _ _ _ _ (hn n).1 (hm n).1
  · change (normalizedWeightedClosingMap hp w ψ N).snd n-
        (normalizedWeightedClosingMap hp w ψ (M+1)).snd n =
      Coeff.truncate (Finset.Icc (-(M:ℤ)) M) (normalizedWeightedClosingMap hp w ψ N-ψ).snd n
    rw [Coeff.truncate_apply]
    exact cutoff_scalar_difference N M hNM n _ _ _ _ (hn n).2 (hm n).2

private theorem fderiv_difference_of_cutoff_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F G : E → E) (P : E →L[ℂ] E) (a : E) (hF : AnalyticAt ℂ F a) (hG : AnalyticAt ℂ G a)
    (he : (fun b => F b-G b) =ᶠ[𝓝 a] fun b => P (F b-b)) :
    fderiv ℂ F a-fderiv ℂ G a = P.comp (fderiv ℂ F a-ContinuousLinearMap.id ℂ E) := by
  have hleft := hF.differentiableAt.hasFDerivAt.sub hG.differentiableAt.hasFDerivAt
  have hright := P.hasFDerivAt.comp a (hF.differentiableAt.hasFDerivAt.sub (hasFDerivAt_id a))
  exact (hleft.congr_of_eventuallyEq he.symm).unique hright

/-- Approximation by finite output projections makes the fixed derivative remainder compact. -/
theorem isCompactOperator_normalizedWeightedClosingMap_fderiv_sub_id_of_mem
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p) (N : ℕ)
    (hA : AnalyticAt ℂ (fun ψ => normalizedWeightedClosingMap hp w ψ N) φ)
    (hmem : ∀ᶠ ψ in 𝓝 φ, ∀ positive : Bool,
      Memℓp (weightedResonantCenterRemainderCoordinate hp w (normalizedWeightedPeriodOne w ψ) N positive) p) :
    IsCompactOperator (fderiv ℂ (fun ψ => normalizedWeightedClosingMap hp w ψ N) φ-
      ContinuousLinearMap.id ℂ (CoeffPair p)) := by
  let T := fderiv ℂ (fun ψ => normalizedWeightedClosingMap hp w ψ N) φ-ContinuousLinearMap.id ℂ (CoeffPair p)
  have hclosed : IsClosed {L : CoeffPair p →L[ℂ] CoeffPair p | IsCompactOperator L} :=
    isClosed_setOfPred_isCompactOperator
  apply hclosed.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r,hr,M₀,_,h⟩ := exists_fixedBall_normalizedWeightedClosingMap_derivative hp hp1 w φ ε hε
  let M := max N M₀
  have hM := h (M+1) (by dsimp [M]; omega)
  have hφ : φ ∈ ball φ (4*r) := mem_ball_self (by positivity)
  have he : (fun ψ => normalizedWeightedClosingMap hp w ψ N-normalizedWeightedClosingMap hp w ψ (M+1)) =ᶠ[𝓝 φ]
      fun ψ => sourceSymmetricTruncateCLM M (normalizedWeightedClosingMap hp w ψ N-ψ) := by
    filter_upwards [hmem,isOpen_ball.mem_nhds hφ] with ψ hψ hψb
    exact normalizedWeightedClosingMap_cutoff_difference hp w ψ N M (by dsimp [M]; omega)
      hψ (hM.2.1 ψ hψb).1
  have hd := fderiv_difference_of_cutoff_germ
    (fun ψ => normalizedWeightedClosingMap hp w ψ N)
    (fun ψ => normalizedWeightedClosingMap hp w ψ (M+1)) (sourceSymmetricTruncateCLM M) φ hA (hM.1 φ hφ) he
  let K := (sourceSymmetricTruncateCLM M).comp T
  have hK : IsCompactOperator K := (isCompactOperator_sourceSymmetricTruncateCLM M).comp_clm T
  refine ⟨K,hK,?_⟩
  rw [dist_eq_norm]
  change ‖T-K‖ < ε
  have herr : T-K = fderiv ℂ (fun ψ => normalizedWeightedClosingMap hp w ψ (M+1)) φ-
      ContinuousLinearMap.id ℂ (CoeffPair p) := by
    change T-(sourceSymmetricTruncateCLM M).comp T = _
    rw [← hd]
    dsimp [T]
    abel
  rw [herr]
  exact hM.2.2.1 φ (mem_ball_self (by positivity))

/-- Construct a common complex neighborhood with compact derivative remainders at every late cutoff. -/
theorem exists_uniform_compact_normalizedWeightedClosingMap_derivative
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p) :
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      AnalyticOnNhd ℂ (fun ψ => normalizedWeightedClosingMap hp w ψ N) (ball φ r) ∧
      ∀ ψ ∈ ball φ r,
        IsCompactOperator (fderiv ℂ (fun χ => normalizedWeightedClosingMap hp w χ N) ψ-
          ContinuousLinearMap.id ℂ (CoeffPair p)) := by
  obtain ⟨r,hr,N₀,hN₀,h⟩ := exists_fixedBall_normalizedWeightedClosingMap_derivative hp hp1 w φ 1 (by norm_num)
  refine ⟨4*r,by positivity,N₀,hN₀,fun N hN => ⟨(h N hN).1,fun ψ hψ => ?_⟩⟩
  apply isCompactOperator_normalizedWeightedClosingMap_fderiv_sub_id_of_mem hp hp1 w ψ N ((h N hN).1 ψ hψ)
  filter_upwards [isOpen_ball.mem_nhds hψ] with χ hχ
  exact ((h N hN).2.1 χ hχ).1

end NLS.ZakharovShabat
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp] theorem normalizedWeightedClosingMap_one (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) :
    normalizedWeightedClosingMap hp SpectralWeight.one φ N = sourceAdaptedClosingMap hp φ N := rfl

/-- The same compact remainder theorem holds for the actual original adapted map. -/
theorem exists_uniform_compact_sourceAdaptedClosingMap_derivative
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      AnalyticOnNhd ℂ (fun ψ => sourceAdaptedClosingMap hp ψ N) (ball φ r) ∧
      ∀ ψ ∈ ball φ r, IsCompactOperator
        (fderiv ℂ (fun χ => sourceAdaptedClosingMap hp χ N) ψ-ContinuousLinearMap.id ℂ (CoeffPair p)) := by
  exact exists_uniform_compact_normalizedWeightedClosingMap_derivative hp hp1 SpectralWeight.one φ
end NLS.ZakharovShabat
