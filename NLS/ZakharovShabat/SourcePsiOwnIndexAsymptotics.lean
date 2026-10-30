import NLS.ZakharovShabat.SourcePsiSharedActualGapMajorant
import NLS.ZakharovShabat.SourceAuxiliaryUniformAsymptotics
import NLS.SequenceSpaces.BoundedScalarProducts

/-! # The own-index product asymptotics in Section 16

One shared majorant controls every deleted branch before selecting its own
Dirichlet root. The positive quotient product is therefore 1 plus an lp
error. Multiplication by the signed omitted standard-root product gives
the separate psi numerator asymptotic, for every real source and finite
p>1, including all central indices and collapsed gaps.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceLemma12_12Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The positive quotient product at its own Dirichlet root has an lp error. -/
theorem original_ownIndex_quotient_error_memlp
    (H : SourceLemma12_12Data hp hp1 W₀ W s) (φ : realTypeSourceSubmodule p) :
    Memℓp (fun n => sourceSingleRootQuotientJointProduct hp hp1 n
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n,
        ((s n φ.val : Coeff p),φ.val))-1) p := by
  have hφW := H.original_theta_common_domain.real_subset φ.property
  obtain ⟨T,_,hφT,_,hb⟩ := H.angular_extension.exists_local_shared_actualGap_quotient_majorant φ hφW
  have hpp : ENNReal.ofReal (p.toReal/2) ≤ p := by
    calc
      ENNReal.ofReal (p.toReal/2) ≤ ENNReal.ofReal p.toReal :=
        ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := p)])
      _ = p := ENNReal.ofReal_toReal hp
  obtain ⟨M,_,hb⟩ := hb p hp hp1 hpp
  obtain ⟨B,_,hB⟩ := hb φ.val hφT
  apply (lp.memℓp B).mono'
  intro n
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n
  let a := sourcePsiFillDeletedRoot n (s n φ.val) (sourceStandardRootMidpoint hp hp1 φ.val n)
  have hfill : sourcePsiCandidate n (μ,a) = sourcePsiCandidate n (μ,(s n φ.val : Coeff p)) :=
    sourcePsiCandidate_eq_of_off_index hp hp1 n μ a _
      (fun k hk => sourcePsiFillDeletedRoot_apply_other n k hk (s n φ.val) _)
  have hprod : jointDeletedSingleSpectralProduct n (μ,a) =
      jointDeletedSingleSpectralProduct n (μ,(s n φ.val : Coeff p)) := by
    dsimp only [sourcePsiCandidate] at hfill
    exact mul_left_cancel₀ (by norm_num : (-2:ℂ) ≠ 0) hfill
  have hq : sourceSingleRootQuotientJointProduct hp hp1 n (μ,((s n φ.val : Coeff p),φ.val)) =
      sourceSingleRootQuotientJointProduct hp hp1 n (μ,(a,φ.val)) := by
    simp only [sourceSingleRootQuotientJointProduct,hprod]
  rw [show canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n = μ from rfl,hq]
  exact hB n n μ
    (canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType hp hp1 .dirichlet φ.val φ.property n)

/-- The actual psi numerator has the signed free asymptotic at its own root. -/
theorem original_ownIndex_psi_error_memlp
    (H : SourceLemma12_12Data hp hp1 W₀ W s) (φ : realTypeSourceSubmodule p) :
    Memℓp (fun n => sourcePsiCandidate n
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n,(s n φ.val : Coeff p))+
        2*cos ((Real.pi:ℂ)*n)) p := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val
  let P := fun n => sourceStandardRootOmittedProduct hp hp1 n φ.val (μ n)
  let Q := fun n => sourceSingleRootQuotientJointProduct hp hp1 n (μ n,((s n φ.val : Coeff p),φ.val))
  have heP : Memℓp (fun n => P n-cos ((Real.pi:ℂ)*n)) p :=
    memlp_sourceStandardRootOmittedProduct_boundary_sub_free hp hp1 .dirichlet φ.val φ.property
  obtain ⟨C,_,hC⟩ := NLS.exists_norm_bound_of_memlp heP
  have hP (n : ℤ) : ‖P n‖ ≤ C+1 := by
    calc
      ‖P n‖ = ‖(P n-cos ((Real.pi:ℂ)*n))+cos ((Real.pi:ℂ)*n)‖ := by rw [sub_add_cancel]
      _ ≤ ‖P n-cos ((Real.pi:ℂ)*n)‖+‖cos ((Real.pi:ℂ)*n)‖ := norm_add_le _ _
      _ ≤ C+1 := by simpa only [cos_freeCenter_eq_natAbs_sign,norm_pow,norm_neg,norm_one,one_pow] using add_le_add (hC n) (le_refl (1:ℝ))
  have hQP := NLS.memlp_smul_of_bounded_vector (fun n => Q n-1) P
    (H.original_ownIndex_quotient_error_memlp φ) (C+1) hP
  convert (hQP.add heP).const_smul (-2:ℂ) using 1
  funext n
  have hPn : P n ≠ 0 := sourceStandardRootOmittedProduct_ne_zero hp hp1 φ.val (μ n) n
    (canonicalPeriodOneBoundaryRoot_mem_omittedDomain hp hp1 .dirichlet φ.val φ.property n)
  simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul]
  change -2*jointDeletedSingleSpectralProduct n (μ n,(s n φ.val : Coeff p))+
    2*cos ((Real.pi:ℂ)*n) =
      -2*((jointDeletedSingleSpectralProduct n (μ n,(s n φ.val : Coeff p))/P n-1)*P n+
        (P n-cos ((Real.pi:ℂ)*n)))
  field_simp
  ring

end NLS.ZakharovShabat.SourceLemma12_12Data
