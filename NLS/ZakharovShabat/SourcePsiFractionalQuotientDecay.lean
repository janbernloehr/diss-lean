import NLS.ZakharovShabat.SourceQuotientFractionalDecay
import NLS.ZakharovShabat.SourcePsiRefinedQuotientTail
import NLS.ZakharovShabat.SourceSobolevSquaredGapBounds
import NLS.SequenceSpaces.WeightedSquareMajorants

/-! Fractional decay of the ACTUAL filled psi quotient, uniformly
before EVERY deleted index and every selected distant complex disc.
The weighted source order and all closed gaps are retained. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem SourcePsiSquaredGapComplexExtension.exists_local_sobolev_filled_quotient_decay
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (t : ℝ) (ht : 0≤t) (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (hu2t : u≤2*t)
    (φ : realTypeSourceSubmodule 2)
    (hφV : normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht) φ.val∈V) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
    ∃ N : ℕ, ∃ ε : ℝ, 0<ε ∧ ∃ T : Set (CoeffPair 2),
      IsOpen T ∧ φ.val∈T ∧ T⊆L ⁻¹' V ∧ ∃ K : ℕ, N<K ∧
        ∃ M : ℝ, 0≤M ∧ ∀ ψ∈T, ∀ n k : ℤ, K≤k.natAbs →
          ∀ z∈sourceIsolatingDisc (by norm_num) (by norm_num) (L φ.val) N ε k,
            Weight.sobolev u k*‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
              (z,(sourcePsiFillDeletedRoot n (s n (L ψ)) (sourceStandardRootMidpoint (by norm_num) (by norm_num) (L ψ) n),L ψ))-1‖≤M := by
  intro L
  have hrφ : L φ.val∈realTypeSourceLocus 2 := normalizedWeightedSource_realType (sourceSobolevSpectralWeight t ht) φ.val φ.property
  obtain ⟨Ta,hTa,hφa,haV,A,hA,hoffset⟩ := hs.locally_uniform_squared_gap_offsets (L φ.val) hφV
  obtain ⟨Tb,hTb,hφb,_hbV,B,_hB,hbeta⟩ := hs.locally_uniform_refined_filled_offsets (L φ.val) hφV
  obtain ⟨N,ε,hε,_hε1,Td,hTd,_hTdc,hφd,C,_R,_H,hC,_hR,_hH,K,hNK,hdata⟩ :=
    exists_local_sourceSingleRootQuotientAsymptotic_data (by norm_num) (by norm_num) (L φ.val) hrφ
  obtain ⟨G,hG,hφG,R,hR,hgap⟩ := exists_local_sobolevSquaredGap_bounds t ht φ.val
  let T := G∩L ⁻¹' ((Ta∩Tb)∩Td)
  have hT : IsOpen T := hG.inter (((hTa.inter hTb).inter hTd).preimage L.continuous)
  have hφT : φ.val∈T := ⟨hφG,⟨hφa,hφb⟩,hφd⟩
  refine ⟨N,ε,hε,T,hT,hφT,(fun ψ hψ => haV hψ.2.1.1),K,hNK,
    sourceFractionalQuotientBound C A B R,sourceFractionalQuotientBound_nonnegative _ _ _ _ (by linarith) hA.le hR,?_⟩
  intro ψ hψ n k hk z hz
  obtain ⟨g,hgnorm,hquad,_hpoint⟩ := hgap ψ hψ.1
  obtain ⟨α,hαn,hα,hαnorm⟩ := hoffset (L ψ) hψ.2.1.1 n
  obtain ⟨β,hβ,hβnorm⟩ := hbeta (L ψ) hψ.2.1.2 n 2 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_hdisp,_hgap,hsep,hsmall,hdom⟩ := hdata (L ψ) hψ.2.2
  let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)
  let a := sourcePsiFillDeletedRoot n (s n (L ψ)) (sourceStandardRootMidpoint (by norm_num) (by norm_num) (L ψ) n)
  have hβfactor (j : ℤ) : β j=(γ j)^2*α j := by
    rw [←hβ j]
    by_cases hj : j=n
    · subst j
      simp only [displacedRoots_sourcePsiFillDeletedRoot_same,sub_self,hαn,mul_zero]
    · rw [displacedRoots_sourcePsiFillDeletedRoot_other n j hj,hα j hj]
      change _=(sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) j)^2*α j
      ring
  exact norm_sourceSingleRootQuotient_sobolev_l1_bound (L φ.val) (L ψ) a β hβ
    u hu0 hu1 A B R hA.le hR hβnorm g hgnorm
    (Coeff.weighted_square_factor_bound t u hu2t γ β α g A hαnorm hquad hβfactor)
    (Coeff.weighted_square_majorant_mono t u hu2t γ g hquad)
    N ε C hC hsep k z hz (hdom a k hk z hz) (hsmall k hk)

end NLS.ZakharovShabat
