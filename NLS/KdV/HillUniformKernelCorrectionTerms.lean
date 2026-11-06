import NLS.KdV.HillUniformSeparatedQuadraticPrimitives
import NLS.KdV.HillUniformNativeDirichletTerminal
import NLS.KdV.HillUniformPointwiseDirichletValue
import NLS.KdV.HillQuadraticDirichletPhysicalMatching
import NLS.KdV.HillUniformRealGapLocalization
import NLS.KdV.HillUniformDirichletPhysical
import NLS.KdV.HillFilledFreeGapPhysical

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- Actual off-diagonal high regular corrections have common analytic
charts and complete separation-kernel bounds in every native weighted
source space. The radius, cutoff and bound precede both n and the weight. -/
theorem exists_hillRegularAbelianCorrection_uniform_native_kernel_charts :
    ∃ δ M : ℝ, ∃ N : ℕ, 0<δ ∧ 0<M ∧ ∃ hN : 1≤N, ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ β : ℕ → Coeff 2 → ℂ,
        (∀ k : ℕ, AnalyticOnNhd ℂ (β k) (ball 0 δ)) ∧
        (∀ k : ℕ, ¬(N≤k ∧ k≠n) → β k=0) ∧
        (∀ w : SpectralWeight, ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖<δ →
          ∀ k : ℕ, ‖β k (hillPeriodOneCoefficientMap w q)‖≤M*hillOffDiagonalPeriodKernel n (k : ℤ)) ∧
        ∀ q : RealPeriodOneHillPotential, ‖q.val‖<δ → ∀ k : ℕ, ∀ hk : N≤k, k≠n →
          β k (SpectralWeight.one.toCoeff q.val)=
            hillRegularAbelianCorrection q.val q.property.1 q.property.2 n hn k (hN.trans hk) := by
  obtain ⟨δ,S,Np,hδ,hS,hNp,hprimitives⟩ := exists_hillSelectedPsi_uniform_separated_quadratic_primitives h0q h0r
  obtain ⟨T,Nt,hT,hNt,hterminal⟩ := exists_hillNativeComplexDirichletGapTerminal_uniform_bound h0q h0r δ hδ.le
  obtain ⟨Nv,hNv,hvalue⟩ := exists_hillComplexQuadraticDirichletValue_uniform_pointwise_bound h0q h0r δ
  obtain ⟨Nr,_,hrootmatch⟩ := exists_hillFilledFreeGapRoot_bounded_real_physical_matching h0q h0r δ
  obtain ⟨Ny,_,hsymmetric⟩ := exists_hillFreeGap_bounded_real_symmetric_data_matching h0q h0r δ
  obtain ⟨Nm,_,hmumatch⟩ := exists_hillScaledDirichletRoot_bounded_real_physical_matching h0q h0r (1/16) (by norm_num) (by norm_num) δ
  obtain ⟨Nl,_,hlocalization⟩ := exists_hillFreeGap_bounded_real_midpoint_halfgap_localization h0q h0r (1/16) (by norm_num) (by norm_num) δ
  obtain ⟨Nd,_,hmuchart⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart h0q h0r (1/16) (by norm_num) (by norm_num) δ
  let N := Np+Nt+Nv+Nr+Ny+Nm+Nl+Nd+1
  let M := T*(36*Real.pi*S)
  have hN : 1≤N := by dsimp only [N];omega
  refine ⟨δ,M,N,hδ,by dsimp only [M];positivity,hN,?_⟩
  intro n hn
  obtain ⟨G,_,hsol,hreal⟩ := hprimitives n hn
  choose H hHa hODE hHb using hsol
  let β : ℕ → Coeff 2 → ℂ := fun k p =>
    if hk : N≤k ∧ k≠n then hillComplexQuadraticDirichletValue h0q h0r
      (H k (by dsimp only [N] at hk;omega) hk.2) k p else 0
  have hval (k : ℕ) (hk : N≤k ∧ k≠n) := hvalue (ball 0 δ) Subset.rfl k
    (by dsimp only [N] at hk;omega) (H k (by dsimp only [N] at hk;omega) hk.2)
    (hHa k (by dsimp only [N] at hk;omega) hk.2)
    (36*Real.pi*S*hillOffDiagonalPeriodKernel n (k : ℤ))
    (hHb k (by dsimp only [N] at hk;omega) hk.2)
  refine ⟨β,?_,?_,?_,?_⟩
  · intro k
    by_cases hk : N≤k ∧ k≠n
    · simpa only [β,dif_pos hk] using (hval k hk).1
    · simpa only [β,dif_neg hk] using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : Coeff 2 => (0:ℂ)) (ball 0 δ))
  · intro k hk
    funext p
    exact dif_neg hk
  · intro w q hq k
    by_cases hk : N≤k ∧ k≠n
    · have hp : hillPeriodOneCoefficientMap w q∈ball 0 δ := by
        rw [mem_ball,dist_zero_right]
        exact (norm_hillPeriodOneCoefficientMap_le w q).trans_lt hq
      have hh := (hval k hk).2 (hillPeriodOneCoefficientMap w q) hp
      change ‖β k (hillPeriodOneCoefficientMap w q)‖≤_ at ⊢
      rw [show β k (hillPeriodOneCoefficientMap w q)=hillComplexQuadraticDirichletValue h0q h0r
        (H k (by dsimp only [N] at hk;omega) hk.2) k (hillPeriodOneCoefficientMap w q) from dif_pos hk]
      apply hh.trans
      have ht := hterminal w q hq.le k (by dsimp only [N] at hk;omega)
      change ‖hillComplexDirichletGapTerminal h0q h0r k (hillPeriodOneCoefficientMap w q)‖≤T at ht
      apply (mul_le_mul_of_nonneg_right ht (mul_nonneg (by positivity : 0≤36*Real.pi*S) (hillOffDiagonalPeriodKernel_nonneg n (k : ℤ)))).trans_eq
      dsimp only [M]
      ring
    · rw [show β k (hillPeriodOneCoefficientMap w q)=0 from dif_neg hk,norm_zero]
      exact mul_nonneg (by dsimp only [M];positivity) (hillOffDiagonalPeriodKernel_nonneg n (k : ℤ))
  · intro q hq k hk hkn
    have hkP : Np≤k := by dsimp only [N] at hk;omega
    have hkR : Nr≤k := by dsimp only [N] at hk;omega
    have hkY : Ny≤k := by dsimp only [N] at hk;omega
    have hkM : Nm≤k := by dsimp only [N] at hk;omega
    have hkL : Nl≤k := by dsimp only [N] at hk;omega
    have hkD : Nd≤k := by dsimp only [N] at hk;omega
    have hk1 : 1≤k := hN.trans hk
    have hp : SpectralWeight.one.toCoeff q.val∈ball 0 δ := by
      rw [mem_ball,dist_zero_right]
      exact (SpectralWeight.one.norm_toCoeff_le q.val).trans_lt hq
    have hpδ : ‖SpectralWeight.one.toCoeff q.val‖≤δ :=
      (SpectralWeight.one.norm_toCoeff_le q.val).trans hq.le
    have hJ : AnalyticOnNhd ℂ (fun E => H k hkP hkn (E,SpectralWeight.one.toCoeff q.val))
        (ball (hillRealGapCenter 0 h0q h0r k : ℂ)
          (3*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4)) := by
      intro E hE
      exact (hHa k hkP hkn (E,SpectralWeight.one.toCoeff q.val) ⟨hE,hp⟩).comp
        (f := fun z : ℂ => (z,SpectralWeight.one.toCoeff q.val)) (analyticAt_id.prod analyticAt_const)
    obtain ⟨hMid,hSq⟩ := hsymmetric q.val q.property.1 q.property.2 hpδ k hkY
    obtain ⟨hτ,hgap⟩ := hlocalization q.val q.property.1 q.property.2 hpδ k hkL
    have hR : 0<hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k :=
      add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1 (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
    have hmuK : hillScaledDirichletRoot h0q h0r (1/16) k (SpectralWeight.one.toCoeff q.val)∈
        closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) :=
      closedBall_subset_closedBall (by linarith : (1/16)*(hillRealGapHalfLength 0 h0q h0r k+
        hillRealGapCollar 0 h0q h0r k)≤hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)
        (ball_subset_closedBall (((hmuchart k hkD).2 _ hpδ).1))
    have hh := hillComplexQuadraticDirichletValue_eq_physical_of_data h0q h0r q.val q.property.1 q.property.2
      n k hn hk1 hkn G (H k hkP hkn) hJ (hODE k hkP hkn _ hp) (hreal q hq)
      (hrootmatch q.val q.property.1 q.property.2 hpδ k hkR) hMid hSq
      (hmumatch q.val q.property.1 q.property.2 hpδ k hkM) hmuK (by linarith) (by linarith)
    simpa only [β,dif_pos (show N≤k ∧ k≠n from ⟨hk,hkn⟩)] using hh

end NLS.KdV
