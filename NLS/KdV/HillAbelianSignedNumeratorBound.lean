import NLS.KdV.HillAbelianOddGapNumerator

/-! Explicit reciprocal signed-index bounds for the ACTUAL Hill gap
numerator, reduced to the actual retained roots and regular factors.
This keeps both signed terms and does not assume a universal scalar. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem norm_abelianGapNumerator_le_signed_factors (P : HillProductEquationPatch) (n m : ℕ+)
    (hmn : m ≠ n) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi q)) :
    ‖P.abelianGapNumerator n m (z,q)‖ ≤
      ‖displacedRoots (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q):Coeff 2) ((m:ℕ):ℤ)-z‖*
        ‖sourcePsiMidpointFilledRegularFactor (by norm_num) (by norm_num) ((n:ℕ):ℤ) ((m:ℕ):ℤ)
          (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q)) (P.sourcePsi q) z‖/
          (Real.pi*|((n:ℕ):ℝ)-(m:ℕ)|)+
      ‖displacedRoots (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q):Coeff 2) (-((m:ℕ):ℤ))+z‖*
        ‖sourcePsiMidpointFilledRegularFactor (by norm_num) (by norm_num) ((n:ℕ):ℤ) (-((m:ℕ):ℤ))
          (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q)) (P.sourcePsi q) (-z)‖/
          (Real.pi*((n:ℕ)+(m:ℕ):ℝ)) := by
  have hm : ((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by exact_mod_cast hmn
  have hneg : -((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by have := n.pos; have := m.pos; omega
  have href : SourcePeriodicReflection (by norm_num) (by norm_num) (P.sourcePsi q) :=
    sourcePeriodicReflection_hillMiuraDiagonal (P.parent.parent.miuraBall.actionBall.lift q)
  rw [P.abelianGapNumerator_eq_signed_difference n m q hq z hz]
  apply (norm_sub_le _ _).trans_eq
  rw [sourceAngularGapNumerator_eq_midpointFilledRegularFactor (by norm_num) (by norm_num)
    ((n:ℕ):ℤ) ((m:ℕ):ℤ) hm _ _ z hz,
    sourceAngularGapNumerator_eq_midpointFilledRegularFactor (by norm_num) (by norm_num)
      ((n:ℕ):ℤ) (-((m:ℕ):ℤ)) hneg _ _ (-z) (href.neg_mem_rootDomain_iff z |>.mpr hz)]
  simp only [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
    Complex.norm_intCast]
  push_cast
  rw [sub_neg_eq_add,sub_neg_eq_add,abs_of_nonneg (by positivity : 0 ≤ ((n:ℕ):ℝ)+(m:ℕ))]

theorem norm_abelianGapNumerator_le_of_signed_bounds (P : HillProductEquationPatch) (n m : ℕ+)
    (hmn : m ≠ n) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi q))
    (A M : ℝ) (hA : 0 ≤ A)
    (hrpos : ‖displacedRoots (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q):Coeff 2) ((m:ℕ):ℤ)-z‖ ≤ A)
    (hrneg : ‖displacedRoots (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q):Coeff 2) (-((m:ℕ):ℤ))+z‖ ≤ A)
    (hχpos : ‖sourcePsiMidpointFilledRegularFactor (by norm_num) (by norm_num) ((n:ℕ):ℤ) ((m:ℕ):ℤ)
      (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q)) (P.sourcePsi q) z‖ ≤ M)
    (hχneg : ‖sourcePsiMidpointFilledRegularFactor (by norm_num) (by norm_num) ((n:ℕ):ℤ) (-((m:ℕ):ℤ))
      (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q)) (P.sourcePsi q) (-z)‖ ≤ M) :
    ‖P.abelianGapNumerator n m (z,q)‖ ≤
      (A*M/Real.pi)*(1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) := by
  apply (P.norm_abelianGapNumerator_le_signed_factors n m hmn q hq z hz).trans
  calc
    _ ≤ A*M/(Real.pi*|((n:ℕ):ℝ)-(m:ℕ)|)+A*M/(Real.pi*((n:ℕ)+(m:ℕ):ℝ)) :=
      add_le_add
        (div_le_div_of_nonneg_right (mul_le_mul hrpos hχpos (norm_nonneg _) hA) (by positivity))
        (div_le_div_of_nonneg_right (mul_le_mul hrneg hχneg (norm_nonneg _) hA) (by positivity))
    _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring

end NLS.KdV.HillProductEquationPatch
