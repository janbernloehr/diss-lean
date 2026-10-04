import NLS.ZakharovShabat.SourceFullAbelianUniformEndpoints
import NLS.ZakharovShabat.SourceSingleRootQuotientTailLimit
import NLS.ZakharovShabat.SourceSquaredGapUniformRowTails

/-! # A source-local uniform bound for the regular critical-root factor

The deleted product estimate is specialized to the canonical critical
sequence. Uniform displacement norms and squared-gap row bounds give one
constant on every distant free disc, for nearby complex sources.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_local_uniform_sourceCriticalRootRatioExtension_tail_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ K : ℕ, ∃ M : ℝ, 0 < M ∧
      ∀ ψ ∈ V, ∀ n : ℤ, K ≤ n.natAbs → ∀ z ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4),
        ‖sourceCriticalRootRatioExtension hp hp1 n ψ z‖ ≤ M := by
  let : Fact (1 ≤ p.conjExponent) := ⟨((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top).le⟩
  obtain ⟨N,ε,_,_,Vq,hVq,_,hφq,C,hC,Kq,hq⟩ :=
    exists_local_uniform_sourceSingleRootQuotientJointProduct_tail_bound (q := p) hp hp1 hp φ hφ
  obtain ⟨Vr,hVr,hφr,Kr,hrow⟩ := exists_uniform_sourceSquaredGapPhysicalRows_half_unit hp hp1 φ C hC
  obtain ⟨_,_,Um,hUm,hφm,Rm,hRm,hm⟩ := exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  obtain ⟨_,_,Uc,hUc,_,hφc,_,Rc,hRc,hc⟩ := exists_uniform_canonicalCriticalPoints hp hp1 (periodOnePotential φ)
  let L := ‖Coeff.puncturedLattice p.conjExponent ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖
  let M := Real.exp (C*(Rc+Rm)*L+1)
  refine ⟨((Vq ∩ Vr) ∩ Um) ∩ (periodOnePotential ⁻¹' Uc),
    ((hVq.inter hVr).inter hUm).inter (hUc.preimage (periodOnePotential (p := p)).continuous),
    ⟨⟨⟨hφq,hφr⟩,hφm⟩,hφc⟩,max (max Kq Kr) (N+1),M,Real.exp_pos _,?_⟩
  intro ψ hψ n hn z hz
  let a := canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let α := a-sourcePeriodicMidpointDisplacement hp hp1 ψ
  have hα : ∀ m : ℤ, displacedRoots a m-canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m = α m := by
    intro m
    simp only [α,lp.coeFn_sub,Pi.sub_apply,sourcePeriodicMidpointDisplacement_apply,displacedRoots]
    ring
  have hαnorm : ‖α‖ ≤ Rc+Rm := (norm_sub_le _ _).trans
    (add_le_add (hc _ hψ.2 (periodOnePotential_mem ψ)).2 (hm ψ hψ.1.2).1)
  have hnq : Kq ≤ n.natAbs := by omega
  have hnr : Kr ≤ n.natAbs := by omega
  have hnN : ¬n.natAbs ≤ N := by omega
  have hzD : z ∈ sourceIsolatingDisc hp hp1 φ N ε n := by
    simpa only [sourceIsolatingDisc,if_neg hnN,refinedResonantDisk] using hz
  have hbound := hq ψ hψ.1.1.1 n hnq a α hα z hzD
  have hrow' := hrow ψ hψ.1.1.2 n hnr
  have hexp : C*‖α‖*L+(C^2/2)*(∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) ≤ C*(Rc+Rm)*L+1 := by
    have hmα := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαnorm (by linarith : 0 ≤ C)) (show 0 ≤ L by dsimp only [L]; exact norm_nonneg _)
    change C*‖α‖*L ≤ C*(Rc+Rm)*L at hmα
    nlinarith
  have hprod : ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))‖ ≤ M := by
    have htri := norm_add_le (sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at htri
    have he := Real.exp_le_exp.mpr hexp
    dsimp [M]
    linarith
  simpa only [sourceCriticalRootRatioExtension,norm_mul,norm_neg,norm_I,one_mul,a] using hprod

end NLS.ZakharovShabat
