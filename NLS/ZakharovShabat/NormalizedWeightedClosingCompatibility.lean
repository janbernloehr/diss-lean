import NLS.ZakharovShabat.NormalizedWeightedSourceTopology
import NLS.ZakharovShabat.NormalizedWeightedClosingDerivative

/-! # Weighted and unweighted adapted maps describe the same source

On one common complex neighborhood, decoding the normalized weighted
adapted map gives the actual unweighted adapted map at every large cutoff.
Both low Fourier coefficients and the moving-center high block agree.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem common_preimages
    {E F G : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
    (J : E → F) (L : E → G) (hJ : Continuous J) (hL : Continuous L)
    (a : E) (U : Set F) (V : Set E) (W : Set G)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (haU : J a ∈ U) (haV : a ∈ V) (haW : L a ∈ W) :
    ∃ Z : Set E, IsOpen Z ∧ a ∈ Z ∧ ∀ x ∈ Z, J x ∈ U ∧ x ∈ V ∧ L x ∈ W := by
  exact ⟨((J ⁻¹' U) ∩ V) ∩ (L ⁻¹' W),
    ((hU.preimage hJ).inter hV).inter (hW.preimage hL),⟨⟨haU,haV⟩,haW⟩,
    fun _ hx => ⟨hx.1.1,hx.1.2,hx.2⟩⟩

/-- The actual adapted map commutes with decoding spectral weights locally. -/
theorem exists_uniform_normalizedWeightedClosingMap_decode
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ψ ∈ U,
        normalizedWeightedSource w (normalizedWeightedClosingMap hp w ψ N) =
          sourceAdaptedClosingMap hp (normalizedWeightedSource w ψ) N := by
  obtain ⟨Nf,hNf,Uf,hoF,hφF,hforget⟩ := exists_uniform_weightedResonantCenter_forget
    hp hp1 w (normalizedWeightedPeriodOne w φ)
  obtain ⟨rw,hrw,Nw,_,hw⟩ := exists_fixedBall_normalizedWeightedClosingMap_derivative hp hp1 w φ 1 (by norm_num)
  obtain ⟨ru,hru,Nu,_,hu⟩ := exists_fixedBall_sourceAdaptedClosingMap_derivative hp hp1 (normalizedWeightedSource w φ) 1 (by norm_num)
  obtain ⟨U,hoU,hφU,hsub⟩ := common_preimages (normalizedWeightedPeriodOne w)
    (normalizedWeightedSource w) (normalizedWeightedPeriodOne w).continuous
    (continuous_normalizedWeightedSource w) φ Uf (ball φ (4*rw))
    (ball (normalizedWeightedSource w φ) (4*ru)) hoF isOpen_ball isOpen_ball
    hφF (mem_ball_self (by positivity)) (mem_ball_self (by positivity))
  refine ⟨max Nf (max Nw Nu),by omega,U,hoU,hφU,?_⟩
  intro N hN ψ hψ
  obtain ⟨hψf,hψw,hψu⟩ := hsub ψ hψ
  have hmw := ((hw N (by omega)).2.1 ψ hψw).1
  have hmu := ((hu N (by omega)).2.1 (normalizedWeightedSource w ψ) hψu).1
  have hf (n : ℤ) (hn : N ≤ n.natAbs) := hforget (normalizedWeightedPeriodOne w ψ) hψf n (by omega)
  have hwcoord := normalizedWeightedClosingMap_apply_of_mem hp w ψ N hmw
  have hucoord := sourceAdaptedClosingMap_apply_of_mem hp (normalizedWeightedSource w ψ) N hmu
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext n
  · change (normalizedWeightedSource w (normalizedWeightedClosingMap hp w ψ N)).fst n =
      (sourceAdaptedClosingMap hp (normalizedWeightedSource w ψ) N).fst n
    rw [normalizedWeightedSource_fst,(hwcoord n).1,(hucoord n).1]
    by_cases hn : N ≤ n.natAbs
    · rw [if_pos hn,if_pos hn,mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)]
      have he := (hf (-n) (by simpa only [Int.natAbs_neg] using hn)).2.2
      rwa [forget_normalizedWeightedPeriodOne] at he
    · rw [if_neg hn,if_neg hn,normalizedWeightedSource_fst]
  · change (normalizedWeightedSource w (normalizedWeightedClosingMap hp w ψ N)).snd n =
      (sourceAdaptedClosingMap hp (normalizedWeightedSource w ψ) N).snd n
    rw [normalizedWeightedSource_snd,(hwcoord n).2,(hucoord n).2]
    by_cases hn : N ≤ n.natAbs
    · rw [if_pos hn,if_pos hn,mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)]
      have he := (hf n hn).2.1
      rwa [forget_normalizedWeightedPeriodOne] at he
    · rw [if_neg hn,if_neg hn,normalizedWeightedSource_snd]

end NLS.ZakharovShabat
