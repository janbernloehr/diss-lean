import NLS.ZakharovShabat.SourceBirkhoffComplexClosingInverse

/-! # A complex bound by the actual adapted closing coordinates

On a complex neighborhood of each real source, every distant Birkhoff
coordinate is bounded by the two signed adapted coordinates. The proof
uses actual complex zeros, local Lipschitz continuity, and the quantitative
lower distance bound for the near-identity adapted map.
-/
noncomputable section
open Set Metric Filter Topology NLS.ComplexAnalysis
open scoped ENNReal NNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem exists_lipschitz_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E → F) (a : E) (hf : AnalyticAt ℂ f a) :
    ∃ L : ℝ≥0, ∃ r : ℝ, 0 < r ∧ LipschitzOnWith L f (ball a r) := by
  obtain ⟨L,S,hS,hLip⟩ := hf.hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hS
  exact ⟨L,r,hr,hLip.mono hsub⟩

private theorem coordinate_bound_of_zero (a b : Coeff p × Coeff p) (n : ℤ) (C : ℝ)
    (hzero : b.1 n = 0 ∧ b.2 n = 0) (hbound : ‖a-b‖ ≤ C) :
    ‖a.1 n‖ ≤ C ∧ ‖a.2 n‖ ≤ C := by
  have h₁ := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    (a-b).1 n).trans ((norm_fst_le (a-b)).trans hbound)
  have h₂ := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    (a-b).2 n).trans ((norm_snd_le (a-b)).trans hbound)
  simpa only [Prod.fst_sub,Prod.snd_sub,lp.coeFn_sub,Pi.sub_apply,hzero.1,hzero.2,sub_zero]
    using And.intro h₁ h₂

private theorem exists_ball_mapsTo
    {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    (f : E → F) (a : E) (δ : ℝ) (hδ : 0 < δ) (hf : ContinuousAt f a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ ball a ε, f x ∈ ball (f a) δ := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hf (ball_mem_nhds (f a) hδ))
  exact ⟨ε,hε,fun _ hx => hball hx⟩

private theorem exists_bound_from_inverse
    (hp : p ≠ ⊤) (f : CoeffPair p → Coeff p × Coeff p)
    (A g : CoeffPair p → CoeffPair p) (φ : CoeffPair p) (r δ : ℝ)
    (hr : 0 < r) (hδ : 0 < δ) (L : ℝ≥0)
    (hLip : LipschitzOnWith L f (ball φ r))
    (hA : AnalyticOnNhd ℂ A (ball φ r))
    (hnear : ∀ ψ ∈ ball φ r,
      ‖fderiv ℂ A ψ-ContinuousLinearMap.id ℂ (CoeffPair p)‖ ≤ (1/2:ℝ))
    (hgV : MapsTo g (ball (A φ) δ) (ball φ r))
    (hright : ∀ y ∈ ball (A φ) δ, A (g y) = y)
    (K : ℕ) (hzero : ∀ n : ℤ, K ≤ n.natAbs → ∀ y ∈ ball (A φ) (δ/2),
      (f (g (sourceDeleteResonance n y))).1 n = 0 ∧ (f (g (sourceDeleteResonance n y))).2 n = 0) :
    ∃ K' : ℕ, K ≤ K' ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, K' ≤ n.natAbs →
        ‖(f ψ).1 n‖ ≤ (2*(L:ℝ))*(‖(A ψ).fst (-n)‖+‖(A ψ).snd n‖) ∧
        ‖(f ψ).2 n‖ ≤ (2*(L:ℝ))*(‖(A ψ).fst (-n)‖+‖(A ψ).snd n‖) := by
  obtain ⟨Kd,hdel⟩ := exists_uniform_sourceDeleteResonance_mapsTo hp (A φ) δ hδ
  obtain ⟨ε,hε,hεA⟩ := exists_ball_mapsTo A φ (δ/2) (by positivity)
    (hA φ (mem_ball_self hr)).continuousAt
  refine ⟨max K Kd,le_max_left _ _,ball φ (min r ε),isOpen_ball,mem_ball_self (lt_min hr hε),?_⟩
  intro ψ hψ n hn
  have hψr : ψ ∈ ball φ r := ball_subset_ball (min_le_left _ _) hψ
  have hψA : A ψ ∈ ball (A φ) (δ/2) := hεA ψ (ball_subset_ball (min_le_right _ _) hψ)
  have hT := hdel n (by omega) hψA
  let χ := g (sourceDeleteResonance n (A ψ))
  have hχr : χ ∈ ball φ r := hgV hT
  have hAχ : A χ = sourceDeleteResonance n (A ψ) := hright _ hT
  have hdist := norm_sub_le_two_mul_norm_image_sub_of_derivative_near_id A φ r hA hnear ψ χ hψr hχr
  rw [hAχ] at hdist
  have hdist' := hdist.trans (mul_le_mul_of_nonneg_left
    (norm_sub_sourceDeleteResonance_le n (A ψ)) (by norm_num : (0:ℝ) ≤ 2))
  have hF := hLip.norm_sub_le hψr hχr
  have hbound := hF.trans (mul_le_mul_of_nonneg_left hdist' L.coe_nonneg)
  apply coordinate_bound_of_zero _ _ n _ (hzero n (by omega) (A ψ) hψA)
  simpa only [mul_assoc,mul_left_comm] using hbound

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- A genuine complex coordinate majorant, with a common constant for all large cutoffs. -/
theorem exists_uniform_complex_closing_bound
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceLocus p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∃ K : ℕ, N ≤ K ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ U ⊆ W ∧
        ∀ ψ ∈ U, ∀ n : ℤ, K ≤ n.natAbs →
          ‖(sourceBirkhoffMap hp hp1 s ψ).1 n‖ ≤ C*
            (‖(sourceAdaptedClosingMap hp ψ N).fst (-n)‖+‖(sourceAdaptedClosingMap hp ψ N).snd n‖) ∧
          ‖(sourceBirkhoffMap hp hp1 s ψ).2 n‖ ≤ C*
            (‖(sourceAdaptedClosingMap hp ψ N).fst (-n)‖+‖(sourceAdaptedClosingMap hp ψ N).snd n‖) := by
  obtain ⟨L,rL,hrL,hLip⟩ := exists_lipschitz_ball (sourceBirkhoffMap hp hp1 s)
    φ.val (D.analytic φ.val (D.real_subset φ.property))
  obtain ⟨rD,hrD,Nd,hNd,hDer⟩ := exists_fixedBall_sourceAdaptedClosingMap_derivative hp hp1 φ.val (1/2) (by norm_num)
  let r := min rL rD
  have hr : 0 < r := lt_min hrL hrD
  have hrLle : r ≤ rL := min_le_left _ _
  have hrDle : r ≤ rD := min_le_right _ _
  obtain ⟨Ni,hNi,hInv⟩ := D.exists_uniform_complex_closing_inverse_within φ (ball φ.val r) isOpen_ball (mem_ball_self hr)
  refine ⟨2*(L:ℝ),by positivity,max Ni Nd,by omega,?_⟩
  intro N hN
  obtain ⟨δ,hδ,g,hg,hgW,_,hdata,Ki,hNKi,hzero⟩ := hInv N (by omega)
  let A := fun ψ => sourceAdaptedClosingMap hp ψ N
  have hA : AnalyticOnNhd ℂ A (ball φ.val r) := (hDer N (by omega)).1.mono
    (ball_subset_ball (by linarith))
  have hnear : ∀ ψ ∈ ball φ.val r,
      ‖fderiv ℂ A ψ-ContinuousLinearMap.id ℂ (CoeffPair p)‖ ≤ (1/2:ℝ) := by
    intro ψ hψ
    exact ((hDer N (by omega)).2.2.1 ψ (ball_subset_ball (by linarith) hψ)).le
  obtain ⟨K,hKiK,U,hoU,hφU,hbound⟩ := exists_bound_from_inverse hp
    (sourceBirkhoffMap hp hp1 s) A g φ.val r δ hr hδ L
    (hLip.mono (ball_subset_ball hrLle)) hA hnear
    (fun y hy => (hgW hy).1) (fun y hy => (hdata y hy).1) Ki hzero
  exact ⟨K,hNKi.trans hKiK,U ∩ W,hoU.inter D.source_open,
    ⟨hφU,D.real_subset φ.property⟩,inter_subset_right,
    fun ψ hψ n hn => hbound ψ hψ.1 n hn⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
