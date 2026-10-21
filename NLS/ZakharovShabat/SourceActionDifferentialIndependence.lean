import NLS.ZakharovShabat.SourceCorollary13_2Original
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # Independence of original complex action differentials

The original action integrals in the introduction, printed p. 9,
have independent differentials precisely on their open-gap index set.
-/

noncomputable section
open Set NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual action differentials at a real source are independent on its open gaps.
Only the selected gaps need to be open; all remaining gaps may collapse. -/
theorem linearIndependent_sourceComplexAction_fderiv_open_gaps
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) :
    LinearIndependent ℂ
      (fun n : {n : ℤ // canonicalPeriodicGap hp hp1
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0} =>
        fderiv ℂ (sourceComplexAction hp hp1 n.val) φ.val) := by
  classical
  obtain ⟨W₀,B,W,s,D,_⟩ := exists_sourceCorollary13_2_regular hp hp1
  rw [linearIndependent_iff']
  intro S a ha n hn
  have hc : (∑ k ∈ S, a k • (sourceActionRegularCotangent hp hp1 k.val φ).coefficients) = 0 := by
    apply Prod.ext <;> ext j
    · have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ =>
        L (CoeffPair.inlCLM (lp.single p j 1))) ha
      simpa only [Prod.fst_sum,Prod.smul_fst,lp.coeFn_sum,Finset.sum_apply,
        lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
        (sourceActionRegularCotangent hp hp1 _ φ).fst_eq,
        sourceActionRegularCotangent_toCotangent,sum_apply,
        smul_apply,zero_apply,Prod.fst_zero,lp.coeFn_zero,Pi.zero_apply] using he
    · have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ =>
        L (CoeffPair.inrCLM (lp.single p j 1))) ha
      simpa only [Prod.snd_sum,Prod.smul_snd,lp.coeFn_sum,Finset.sum_apply,
        lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
        (sourceActionRegularCotangent hp hp1 _ φ).snd_eq,
        sourceActionRegularCotangent_toCotangent,sum_apply,
        smul_apply,zero_apply,Prod.snd_zero,lp.coeFn_zero,Pi.zero_apply] using he
  have he := congrArg
    (fun z => hilbertPairBivector (D.thetaRegularCotangent n.val φ n.property).coefficients z) hc
  have hk (k : {k : ℤ // canonicalPeriodicGap hp hp1
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k ≠ 0}) :
      hilbertPairBivector (D.thetaRegularCotangent n.val φ n.property).coefficients
        (sourceActionRegularCotangent hp hp1 k.val φ).coefficients = if k = n then 1 else 0 := by
    change (D.thetaRegularCotangent n.val φ n.property).bivector
      (sourceActionRegularCotangent hp hp1 k.val φ) = _
    rw [D.thetaActionRegular_bivector_eq_kronecker]
    by_cases hkn : k = n
    · subst k
      simp only [ite_true]
    · have hv : n.val ≠ k.val := fun h => hkn (Subtype.ext h.symm)
      rw [if_neg hv,if_neg hkn]
  simp only [map_sum,map_smul,map_zero,smul_eq_mul,hk] at he
  simpa only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',if_pos hn] using he

/-- The same independence holds for the original indexed contour actions themselves. -/
theorem linearIndependent_sourceIndexedAction_fderiv_open_gaps
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) :
    LinearIndependent ℂ
      (fun n : {n : ℤ // canonicalPeriodicGap hp hp1
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0} =>
        fderiv ℂ (sourceIndexedAction hp hp1 n.val) φ.val) := by
  obtain ⟨W₀,_,_,_,W,_,_,_,s,H⟩ := sourceLemma12_12 hp hp1
  have he : (fun n : {n : ℤ // canonicalPeriodicGap hp hp1
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0} =>
        fderiv ℂ (sourceIndexedAction hp hp1 n.val) φ.val) =
      (fun n : {n : ℤ // canonicalPeriodicGap hp hp1
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0} =>
        fderiv ℂ (sourceComplexAction hp hp1 n.val) φ.val) := by
    funext n
    exact H.action_original_fderiv_eq_complexAction φ.val
      (H.original_theta_common_domain.real_subset φ.property) φ.property n.val
  rw [he]
  exact linearIndependent_sourceComplexAction_fderiv_open_gaps hp hp1 φ

end NLS.ZakharovShabat
