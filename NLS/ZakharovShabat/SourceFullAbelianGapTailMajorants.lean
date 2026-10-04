import NLS.ZakharovShabat.SourceCriticalFactorDiscMajorants
import NLS.ZakharovShabat.SourceFullAbelianUniformGapComparison

/-! # The mixed sequence error on distant gaps in Lemma 19.4

The deleted-factor majorants and the actual critical offset combine into
locally bounded `ell^q + ell^(p/2)` majorants for the gap-normalized error
of the actual primitive. Every finite `q > 1` is allowed, and the proof
includes the quasi-norm range `1 < p < 2`.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- One source neighborhood and one sequence-norm bound control both
boundary errors on all distant complex gaps. No asymptotic hypothesis
on the primitive or the deleted factor is supplied by the caller. -/
theorem exists_local_sourceFullAbelian_gap_tail_majorants
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ K : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ ψ ∈ V, ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
        ‖Bq‖ ≤ M ∧ ‖Bg‖ ≤ M ∧
        ∀ (W : Set (CoeffPair p)) (C : SourceFullAbelianUniformCauchyFamily hp hp1 W),
          ψ ∈ ball C.discs.source.val C.discs.sourceRadius →
          ∀ n : ℤ, K ≤ n.natAbs → ∀ θ ∈ Icc (0:ℝ) Real.pi, ∀ upper : Bool,
            ‖C.gapBoundary n ψ θ upper-I*sourceStandardRootGapBoundary hp hp1 ψ n θ upper‖ ≤
              ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖*(‖Bq n‖+‖Bg n‖) := by
  obtain ⟨Vf,hVf,hφf,Kf,F,hF,hfactor⟩ :=
    exists_local_sourceCriticalFactor_mixed_majorants hp hp1 hq hq1 φ hφ
  obtain ⟨Vc,hVc,hφc,A,hA,_,_,hcomp⟩ :=
    exists_local_uniform_sourceFullAbelian_gap_comparison hp hp1 φ hφ
  obtain ⟨Vo,hVo,hφo,L,hL,hoff⟩ := exists_local_uniform_sourceCriticalHalfOffsets hp hp1 φ hφ
  obtain ⟨N,ε,_,_,Vd,hVd,_,hφd,hcluster,_⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ hφ
  let ρ := ENNReal.ofReal (p.toReal/2)
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hρ0 : 0 < ρ.toReal := by dsimp [ρ]; rw [ENNReal.toReal_ofReal (by positivity)]; positivity
  have hρ : ρ ≠ 0 := by intro he; rw [he,ENNReal.toReal_zero] at hρ0; exact lt_irrefl _ hρ0
  let T := max (A*F+L) (((A*F)^ρ.toReal+L^ρ.toReal)^ρ.toReal⁻¹)
  have hT : 0 ≤ T := le_trans (by positivity : 0 ≤ A*F+L) (le_max_left _ _)
  refine ⟨((Vf ∩ Vc) ∩ Vo) ∩ Vd,((hVf.inter hVc).inter hVo).inter hVd,
    ⟨⟨⟨hφf,hφc⟩,hφo⟩,hφd⟩,max Kf (N+1),max (Real.pi*A*F) (Real.pi*T),by positivity,?_⟩
  intro ψ hψ
  obtain ⟨Bq,Bg,hBq,hBg,hpoint⟩ := hfactor ψ hψ.1.1.1
  let D : Coeff ρ := (A:ℂ) • Coeff.magnitude Bg+Coeff.magnitude (sourceCriticalGapLinearOffset hp hp1 ψ)
  let Rq : Coeff q := ((Real.pi*A:ℝ):ℂ) • Coeff.magnitude Bq
  let Rg : Coeff ρ := (Real.pi:ℂ) • D
  have hDn : ‖D‖ ≤ T := by
    apply Coeff.norm_add_le_uniform hρ0
    · rw [lp.norm_const_smul hρ,Coeff.norm_magnitude_quasi hρ,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos hA]
      exact mul_le_mul_of_nonneg_left hBg hA.le
    · rw [Coeff.norm_magnitude_quasi hρ]
      exact (hoff ψ hψ.1.2).2.1
  refine ⟨Rq,Rg,?_,?_,?_⟩
  · have hn : ‖Rq‖ ≤ Real.pi*A*F := by
      dsimp only [Rq]
      rw [norm_smul,Coeff.norm_magnitude,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (mul_pos Real.pi_pos hA)]
      exact mul_le_mul_of_nonneg_left hBq (mul_pos Real.pi_pos hA).le
    exact hn.trans (le_max_left _ _)
  · have hn : ‖Rg‖ ≤ Real.pi*T := by
      dsimp only [Rg]
      rw [lp.norm_const_smul hρ,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      exact mul_le_mul_of_nonneg_left hDn Real.pi_pos.le
    exact hn.trans (le_max_right _ _)
  · intro W C hψC n hn θ hθ upper
    have he : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ n,
        ‖sourceSingleRootQuotientJointProduct hp hp1 n
          (z,(canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ),ψ))-1‖ ≤
            ‖Bq n‖+‖Bg n‖ := by
      intro z hz
      have hzD := sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ N ε n (hcluster ψ hψ.2 n) hz
      apply hpoint n (by omega) z
      simpa only [sourceIsolatingDisc,if_neg (show ¬n.natAbs ≤ N by omega),refinedResonantDisk] using hzD
    have hb := (hcomp ψ hψ.1.1.2).2 W C hψC n (‖Bq n‖+‖Bg n‖)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)) he θ hθ upper
    have hRq : ‖Rq n‖ = Real.pi*A*‖Bq n‖ := by
      simp only [Rq,lp.coeFn_smul,Pi.smul_apply,norm_smul,Coeff.magnitude_apply,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos (mul_pos Real.pi_pos hA),abs_of_nonneg (norm_nonneg _)]
    have hRg : ‖Rg n‖ = Real.pi*(A*‖Bg n‖+‖sourceCriticalGapLinearOffset hp hp1 ψ n‖) := by
      simp only [Rg,D,lp.coeFn_smul,Pi.smul_apply,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,
        smul_eq_mul,← Complex.ofReal_mul,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ Real.pi*(A*‖Bg n‖+‖sourceCriticalGapLinearOffset hp hp1 ψ n‖))]
    rw [hRq,hRg,sourceCriticalGapLinearOffset_apply,norm_mul]
    convert hb using 1
    ring

end NLS.ZakharovShabat
