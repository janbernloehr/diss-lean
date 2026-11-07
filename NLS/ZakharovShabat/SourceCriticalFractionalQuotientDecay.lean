import NLS.ZakharovShabat.SourceQuotientFractionalDecay
import NLS.ZakharovShabat.SourceCriticalHalfExponentOffsets
import NLS.ZakharovShabat.SourceSobolevSquaredGapBounds
import NLS.SequenceSpaces.WeightedSquareMajorants

/-! Fractional decay of the ACTUAL critical-root quotient on original
weighted complex source neighborhoods. No spectral asymptotic is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_local_sobolev_critical_quotient_decay
    (t : ℝ) (ht : 0≤t) (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (hu2t : u≤2*t)
    (φ : realTypeSourceSubmodule 2) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
    ∃ N : ℕ, ∃ ε : ℝ, 0<ε ∧ ∃ T : Set (CoeffPair 2),
      IsOpen T ∧ φ.val∈T ∧ ∃ K : ℕ, N<K ∧ ∃ M : ℝ, 0≤M ∧
        ∀ ψ∈T, ∀ k : ℤ, K≤k.natAbs →
          ∀ z∈sourceIsolatingDisc (by norm_num) (by norm_num) (L φ.val) N ε k,
            Weight.sobolev u k*‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
              (z,(canonicalCriticalDisplacement (by norm_num) (by norm_num)
                (periodOnePotential (L ψ)) (periodOnePotential_mem (L ψ)),L ψ))-1‖≤M := by
  intro L
  have hrφ : L φ.val∈realTypeSourceLocus 2 := normalizedWeightedSource_realType (sourceSobolevSpectralWeight t ht) φ.val φ.property
  obtain ⟨Vq,hVq,hφq,B,hB,hquot⟩ :=
    exists_local_uniform_sourceCriticalGapQuotient (by norm_num) (by norm_num) (L φ.val) hrφ
  obtain ⟨Vo,hVo,hφo,A,_hA,hoff⟩ :=
    exists_local_uniform_sourceCriticalHalfOffsets (by norm_num) (by norm_num) (L φ.val) hrφ
  obtain ⟨N,ε,hε,_hε1,Td,hTd,_hTdc,hφd,C,_R,_H,hC,_hR,_hH,K,hNK,hdata⟩ :=
    exists_local_sourceSingleRootQuotientAsymptotic_data (by norm_num) (by norm_num) (L φ.val) hrφ
  obtain ⟨G,hG,hφG,R,hR,hgap⟩ := exists_local_sobolevSquaredGap_bounds t ht φ.val
  let T := G∩L ⁻¹' ((Vq∩Vo)∩Td)
  have hT : IsOpen T := hG.inter (((hVq.inter hVo).inter hTd).preimage L.continuous)
  have hφT : φ.val∈T := ⟨hφG,⟨hφq,hφo⟩,hφd⟩
  refine ⟨N,ε,hε,T,hT,hφT,K,hNK,sourceFractionalQuotientBound C B A R,
    sourceFractionalQuotientBound_nonnegative _ _ _ _ (by linarith) hB hR,?_⟩
  intro ψ hψ k hk z hz
  obtain ⟨g,hgnorm,hquad,_hpoint⟩ := hgap ψ hψ.1
  have : Fact (1≤ENNReal.ofReal ((2 : ℝ≥0∞).toReal/2)) := ⟨by norm_num⟩
  let α : Coeff 2 := Coeff.exponentInclusion (by norm_num : ENNReal.ofReal ((2 : ℝ≥0∞).toReal/2)≤2)
    (sourceCriticalHalfGapOffset (by norm_num) (by norm_num) (L ψ))
  let b := sourceCriticalGapQuotient (by norm_num) (by norm_num) (L ψ)
  let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)
  let a := canonicalCriticalDisplacement (by norm_num) (by norm_num) (periodOnePotential (L ψ)) (periodOnePotential_mem (L ψ))
  have hαnorm : ‖α‖≤A := (Coeff.norm_exponentInclusion_le _ _).trans (hoff (L ψ) hψ.2.1.2).1
  have hα (j : ℤ) : displacedRoots a j-
      canonicalPeriodicMidpoint (by norm_num) (by norm_num) (periodOnePotential (L ψ)) (periodOnePotential_mem (L ψ)) j=α j := by
    simp only [a,displacedRoots,canonicalCriticalDisplacement_apply,add_sub_cancel]
    exact ((hoff (L ψ) hψ.2.1.2).2.2 j).1
  have hfactor (j : ℤ) : α j=(γ j)^2*b j := by
    simp only [α,Coeff.exponentInclusion_apply,sourceCriticalHalfGapOffset_apply]
    rfl
  obtain ⟨_hdisp,_hgap,hsep,hsmall,hdom⟩ := hdata (L ψ) hψ.2.2
  exact norm_sourceSingleRootQuotient_sobolev_l1_bound (L φ.val) (L ψ) a α hα
    u hu0 hu1 B A R hB hR hαnorm g hgnorm
    (Coeff.weighted_square_factor_bound t u hu2t γ α b g B (hquot (L ψ) hψ.2.1.1).1 hquad hfactor)
    (Coeff.weighted_square_majorant_mono t u hu2t γ g hquad)
    N ε C hC hsep k z hz (hdom a k hk z hz) (hsmall k hk)

end NLS.ZakharovShabat
