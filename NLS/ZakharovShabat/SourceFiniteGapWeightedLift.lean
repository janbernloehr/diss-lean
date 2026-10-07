import NLS.ZakharovShabat.NormalizedWeightedTruncation

/-! # Analytic weighted lifts of nearby sources with a fixed gap tail

Near a finite-gap source that belongs to a given spectral weight, a
single analytic function reconstructs its normalized weighted coordinates
from finitely many original coefficients. On the real sources with a
fixed closed-gap tail, decoding the lift is the identity. The identification
uses the proved lower distance bound for the original closing map.
-/
noncomputable section
open Set Metric Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Nearby real sources with a fixed closed-gap tail admit one actual
complex analytic weighted lift through any finite-gap weighted base point. -/
theorem exists_analyticAt_sourceFiniteGap_weightedLift
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ))
    (hf : (⟨normalizedWeightedSource w φ, normalizedWeightedSource_realType w φ hreal⟩ : realTypeSourceLocus p)
      ∈ sourceFiniteGapLocus hp hp1) (K : ℕ) :
    ∃ f : CoeffPair p → CoeffPair p,
      AnalyticAt ℂ f (normalizedWeightedSource w φ) ∧
      f (normalizedWeightedSource w φ) = φ ∧
      ∀ᶠ ψ in 𝓝 (normalizedWeightedSource w φ),
        IsRealType (CoeffPair.toMax p ψ) →
        (∀ n : ℤ, K ≤ n.natAbs →
          canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) →
        normalizedWeightedSource w (f ψ) = ψ := by
  let a := normalizedWeightedSource w φ
  obtain ⟨δ,hδ,N₀,_,hI⟩ := exists_uniform_real_normalizedWeightedClosingInverse_support hp hp1 w φ hreal
  obtain ⟨N₁,_,hbase⟩ := exists_normalizedWeightedClosingMap_eq_truncate_of_finiteGap hp hp1 w φ hreal hf
  obtain ⟨N₂,_,U,ho,ha,htrunc⟩ := exists_uniform_sourceAdaptedClosingMap_eq_truncate hp hp1 a
  obtain ⟨r,hr,N₃,_,hD⟩ := exists_fixedBall_sourceAdaptedClosingMap_derivative hp hp1 a (1/4) (by norm_num)
  let N := max N₀ (max N₁ (max N₂ (max N₃ K)))
  have hN₀ : N₀ ≤ N := by dsimp [N]; omega
  have hN₁ : N₁ ≤ N := by dsimp [N]; omega
  have hN₂ : N₂ ≤ N := by dsimp [N]; omega
  have hN₃ : N₃ ≤ N := by dsimp [N]; omega
  have hK : K ≤ N := by dsimp [N]; omega
  obtain ⟨g,hg,hgbase,hgdata⟩ := hI N hN₀
  let T := normalizedWeightedTruncateCLM (p := p) w N
  have hTa : T a = normalizedWeightedClosingMap hp w φ N := (hbase N hN₁).symm
  have hTaBall : T a ∈ ball (normalizedWeightedClosingMap hp w φ N) δ := by
    rw [hTa]
    exact mem_ball_self hδ
  let f : CoeffPair p → CoeffPair p := fun ψ => g (T ψ)
  have hfA : AnalyticAt ℂ f a := (hg _ hTaBall).comp (T.analyticAt a)
  have hfa : f a = φ := by dsimp only [f]; rw [hTa,hgbase]
  have hdecode : ContinuousAt (fun ψ => normalizedWeightedSource w (f ψ)) a :=
    (continuous_normalizedWeightedSource w).continuousAt.comp hfA.continuousAt
  have hdecodeBall : ∀ᶠ ψ in 𝓝 a, normalizedWeightedSource w (f ψ) ∈ ball a r :=
    hdecode.eventually (isOpen_ball.mem_nhds (by
      change normalizedWeightedSource w (f a) ∈ ball a r
      rw [hfa]
      exact mem_ball_self hr))
  have htargetBall : ∀ᶠ ψ in 𝓝 a, T ψ ∈ ball (normalizedWeightedClosingMap hp w φ N) δ :=
    T.continuous.continuousAt.eventually (isOpen_ball.mem_nhds hTaBall)
  refine ⟨f,hfA,hfa,?_⟩
  filter_upwards [ho.mem_nhds ha,isOpen_ball.mem_nhds (mem_ball_self hr),hdecodeBall,htargetBall]
    with ψ hψU hψBall hdecodeBall htargetBall
  intro hψReal hψGap
  have hi := hgdata (T ψ) htargetBall
  have hw := (hi.2.2.2 (normalizedWeightedTruncateCLM_support w N ψ)).2
    (normalizedWeightedTruncateCLM_realType w N ψ hψReal)
  have hu := htrunc ψ hψU hψReal N hN₂ (fun n hn => hψGap n (hK.trans hn))
  have hsame : sourceAdaptedClosingMap hp (normalizedWeightedSource w (f ψ)) N =
      sourceAdaptedClosingMap hp ψ N := by
    exact hw.trans ((normalizedWeightedSource_truncate w N ψ).trans hu.symm)
  have hd := hD N hN₃
  have hA : AnalyticOnNhd ℂ (fun χ => sourceAdaptedClosingMap hp χ N) (ball a r) :=
    fun χ hχ => hd.1 χ (ball_subset_ball (by linarith) hχ)
  have hnear (χ : CoeffPair p) (hχ : χ ∈ ball a r) :
      ‖fderiv ℂ (fun ξ => sourceAdaptedClosingMap hp ξ N) χ-ContinuousLinearMap.id ℂ (CoeffPair p)‖ ≤ (1/2 : ℝ) :=
    (hd.2.2.1 χ (ball_subset_ball (by linarith) hχ)).le.trans (by norm_num)
  have hb := norm_sub_le_two_mul_norm_image_sub_of_derivative_near_id
    (fun χ => sourceAdaptedClosingMap hp χ N) a r hA hnear
    (normalizedWeightedSource w (f ψ)) ψ hdecodeBall hψBall
  rw [hsame,sub_self,norm_zero,mul_zero] at hb
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)

/-- A differentiable original curve with one closed-gap tail has a
locally differentiable weighted lift through its weighted base point. -/
theorem exists_differentiableAt_sourceFiniteGap_weightedLift
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ))
    (hf : (⟨normalizedWeightedSource w φ, normalizedWeightedSource_realType w φ hreal⟩ : realTypeSourceLocus p)
      ∈ sourceFiniteGapLocus hp hp1) (K : ℕ) (γ : ℝ → CoeffPair p) (time : ℝ)
    (hγ : DifferentiableAt ℝ γ time) (hbase : γ time = normalizedWeightedSource w φ)
    (hrealγ : ∀ᶠ t in 𝓝 time, IsRealType (CoeffPair.toMax p (γ t)))
    (hgapγ : ∀ᶠ t in 𝓝 time, ∀ n : ℤ, K ≤ n.natAbs →
      canonicalPeriodicGap hp hp1 (periodOnePotential (γ t)) (periodOnePotential_mem (γ t)) n = 0) :
    ∃ ξ : ℝ → CoeffPair p, DifferentiableAt ℝ ξ time ∧ ξ time = φ ∧
      ∀ᶠ t in 𝓝 time, normalizedWeightedSource w (ξ t) = γ t := by
  obtain ⟨f,hfA,hfbase,hfdecode⟩ := exists_analyticAt_sourceFiniteGap_weightedLift hp hp1 w φ hreal hf K
  have hfAt : DifferentiableAt ℝ f (γ time) := by
    rw [hbase]
    exact hfA.differentiableAt.restrictScalars ℝ
  refine ⟨fun t => f (γ t),hfAt.comp time hγ,by change f (γ time) = φ; rw [hbase,hfbase],?_⟩
  have hdecode := hγ.continuousAt.eventually (by rw [hbase]; exact hfdecode)
  filter_upwards [hdecode,hrealγ,hgapγ] with t ht hr hg
  exact ht hr hg

end NLS.ZakharovShabat
