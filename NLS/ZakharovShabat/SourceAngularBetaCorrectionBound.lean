import NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomain

/-! # Locally uniform scalar bounds for the actual beta corrections

The existing reciprocal beta estimate and Hölder summation give one
bound for every correction index. The gap and Dirichlet-minus-midpoint
sequence norms are bounded on the same source neighborhood.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- One neighborhood controls the spectral sequence norms and every
beta correction, at each complex source of the angular domain. -/
theorem exists_local_uniform_betaCorrection_bound
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (φ : CoeffPair p) (hφ : φ ∈ B) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ B ∧
      ∃ G A : ℝ, 0 ≤ G ∧ 0 ≤ A ∧ ∀ ψ ∈ U,
        (‖sourcePeriodicGapDisplacement hp hp1 ψ‖ +
          ‖sourceDirichletMidpointDisplacement hp hp1 ψ‖ ≤ G) ∧
        ∀ n : ℤ, ‖sourceAngularBetaCorrection hp hp1 n s ψ‖ ≤ A := by
  obtain ⟨Vb,hVb,hφb,hVbB,C,hC,hbeta⟩ := D.beta_bound φ hφ
  obtain ⟨_,_,Vg,hVg,hφg,G,hG,hgap⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : 0 < (1:ℝ))
  obtain ⟨_,_,Vm,hVm,hφm,M,hM,hmid⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ (by norm_num : 0 < (1:ℝ))
  let L := ‖sourceBoundaryDisplacement hp hp1 .dirichlet φ‖+1
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hevent : ∀ᶠ ψ in 𝓝 φ, ‖sourceBoundaryDisplacement hp hp1 .dirichlet ψ‖ < L :=
    (D.boundary_analytic .dirichlet φ hφ).continuousAt.norm.eventually
      (gt_mem_nhds (by dsimp only [L]; linarith))
  obtain ⟨Vd,hVdsub,hVd,hφd⟩ := _root_.mem_nhds_iff.mp hevent
  let Q := ‖Coeff.puncturedLattice p.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖
  have hQ : 0 ≤ Q := lp.norm_nonneg' _
  let H := G+(L+M)
  refine ⟨((Vb ∩ Vg) ∩ Vm) ∩ Vd,((hVb.inter hVg).inter hVm).inter hVd,
    ⟨⟨⟨hφb,hφg⟩,hφm⟩,hφd⟩,(fun ψ hψ => hVbB hψ.1.1.1),H,C*H*Q,
    by dsimp only [H]; positivity,by dsimp only [H]; positivity,?_⟩
  intro ψ hψ
  have hdn : ‖sourceDirichletMidpointDisplacement hp hp1 ψ‖ ≤ L+M :=
    (norm_sub_le _ _).trans (add_le_add (hVdsub hψ.2).le (hmid ψ hψ.1.2).1)
  have hn : ‖sourcePeriodicGapDisplacement hp hp1 ψ‖+
      ‖sourceDirichletMidpointDisplacement hp hp1 ψ‖ ≤ H :=
    add_le_add (hgap ψ hψ.1.1.2).1 hdn
  refine ⟨hn,?_⟩
  intro n
  obtain ⟨hsum,hbound⟩ := summable_norm_sourceAngularBetaSeriesTerm_of_bound hp hp1 n s ψ C hC.le
    (hbeta ψ hψ.1.1.1 n)
  exact (norm_tsum_le_tsum_norm hsum).trans (hbound.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hC.le) hQ))

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
