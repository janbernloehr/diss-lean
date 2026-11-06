import NLS.SequenceSpaces.PeriodOneHminusOneDensity
import NLS.SequenceSpaces.DeletedCoordinate

/-! # Mean-zero distributional linear maps are determined by literal L2 inputs -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS

theorem continuousLinearMap_eq_on_meanZero_of_periodOneL2Inclusion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L M : PeriodOneHminusOne →L[ℂ] E)
    (he : ∀ u : Coeff 2, u 0=0 → L (periodOneL2Inclusion u)=M (periodOneL2Inclusion u))
    (q : PeriodOneHminusOne) (hq : q.val 0=0) : L q=M q := by
  let c := periodOneL2Inclusion (lp.single 2 0 (1 : ℂ))
  let Q : PeriodOneHminusOne →L[ℂ] PeriodOneHminusOne :=
    ContinuousLinearMap.id ℂ _-(WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 0).smulRight c
  have hQ (u : Coeff 2) : Q (periodOneL2Inclusion u)=periodOneL2Inclusion (Coeff.deleteCoordinate 0 u) := by
    apply Subtype.ext
    funext j
    simp only [Q,sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,
      WeightedCoeff.sub_val,WeightedCoeff.smul_val,WeightedCoeff.evalCLM_apply,
      c,periodOneL2Inclusion_apply]
    change u j-u 0*((lp.single 2 0 (1 : ℂ) : Coeff 2) j)=u j-((lp.single 2 0 (u 0) : Coeff 2) j)
    by_cases hj : j=0 <;> simp [lp.single_apply,hj]
  have hfix : Q q=q := by
    change q-q.val 0 • c=q
    rw [hq,zero_smul,sub_zero]
  have hh := eqOn_of_eqOn_periodOneL2Inclusion isOpen_univ
    (L.continuous.comp Q.continuous).continuousOn
    (M.continuous.comp Q.continuous).continuousOn (fun u _ => by
      change L (Q (periodOneL2Inclusion u))=M (Q (periodOneL2Inclusion u))
      rw [hQ]
      exact he _ (Coeff.deleteCoordinate_apply_same 0 u))
  simpa only [Function.comp_def,hfix] using hh (mem_univ q)

end NLS
