import NLS.ZakharovShabat.SourceAngularOriginalBetaSeries

/-! # One local bound for every actual original absolute correction series -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem exists_local_uniform_absolute_beta_bound
    (H : SourceLemma12_12Data hp hp1 W₀ W s) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ A : ℝ, 0 < A ∧ ∀ ψ ∈ U, ∀ n : ℤ,
        Summable (fun m : ℤ => ‖sourceAngularBetaSeriesTerm hp hp1 n s ψ m‖) ∧
        (∑' m : ℤ, ‖sourceAngularBetaSeriesTerm hp hp1 n s ψ m‖) ≤ A := by
  obtain ⟨Vb,hVb,hφb,hVbW,C,hC,hbeta⟩ := H.beta_original_uniform_bound φ hφ
  obtain ⟨_,_,Vg,hVg,hφg,G,hG,hgap⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : 0 < (1:ℝ))
  obtain ⟨_,_,Vm,hVm,hφm,M,hM,hmid⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ (by norm_num : 0 < (1:ℝ))
  let L := ‖sourceBoundaryDisplacement hp hp1 .dirichlet φ‖+1
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hevent : ∀ᶠ ψ in 𝓝 φ, ‖sourceBoundaryDisplacement hp hp1 .dirichlet ψ‖ < L :=
    (H.boundary_original_displacement_analytic .dirichlet φ hφ).continuousAt.norm.eventually
      (gt_mem_nhds (by dsimp only [L]; linarith))
  obtain ⟨Vd,hVdsub,hVd,hφd⟩ := _root_.mem_nhds_iff.mp hevent
  let Q := ‖Coeff.puncturedLattice p.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖
  have hQ : 0 ≤ Q := lp.norm_nonneg' _
  let R := G+(L+M)
  refine ⟨((Vb ∩ Vg) ∩ Vm) ∩ Vd,((hVb.inter hVg).inter hVm).inter hVd,
    ⟨⟨⟨hφb,hφg⟩,hφm⟩,hφd⟩,(fun ψ hψ => hVbW hψ.1.1.1),C*R*Q+1,by dsimp only [R]; positivity,?_⟩
  intro ψ hψ
  have hdn : ‖sourceDirichletMidpointDisplacement hp hp1 ψ‖ ≤ L+M :=
    (norm_sub_le _ _).trans (add_le_add (hVdsub hψ.2).le (hmid ψ hψ.1.2).1)
  have hn : ‖sourcePeriodicGapDisplacement hp hp1 ψ‖+
      ‖sourceDirichletMidpointDisplacement hp hp1 ψ‖ ≤ R :=
    add_le_add (hgap ψ hψ.1.1.2).1 hdn
  intro n
  obtain ⟨hsum,hbound⟩ := summable_norm_sourceAngularBetaSeriesTerm_of_bound hp hp1 n s ψ C hC.le
    (hbeta ψ hψ.1.1.1 n)
  exact ⟨hsum,(hbound.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hC.le) hQ)).trans (by linarith)⟩


end SourceLemma12_12Data
end NLS.ZakharovShabat
