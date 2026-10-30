import NLS.ZakharovShabat.SourcePsiDoubleOmittedProduct
import NLS.ZakharovShabat.SourceCorollary10_6

/-!
# Full joint analyticity of the literal auxiliary product

The unused root can be filled locally away from the spectral point.
The single quotient representation then proves analyticity on the entire
natural omitted-gap domain, including numerator-root collisions.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Joint analyticity of the literal regular factor for arbitrary root inputs, including collisions. -/
theorem SourceCorollary10_6Data.zeta_joint_analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (n m : ℤ) (hmn : m ≠ n) :
    AnalyticOnNhd ℂ
      (fun q : ℂ × (Coeff p × CoeffPair p) => sourcePsiZeta hp hp1 n m q.2.1 q.2.2 q.1)
      (sourceSingleRootQuotientJointDomain hp hp1 W m) := by
  intro t ht
  let ξ := t.1+1
  let fill : ℂ × (Coeff p × CoeffPair p) → ℂ × (Coeff p × CoeffPair p) :=
    fun q => (q.1,(Coeff.deleteCoordinate n q.2.1+lp.single p n (ξ-(Real.pi:ℂ)*n),q.2.2))
  have hfill (q : ℂ × (Coeff p × CoeffPair p)) : AnalyticAt ℂ fill q := by
    have ha : AnalyticAt ℂ
        (fun q : ℂ × (Coeff p × CoeffPair p) =>
          Coeff.deleteCoordinate n q.2.1+lp.single p n (ξ-(Real.pi:ℂ)*n)) q :=
      (((Coeff.deleteCoordinate n).analyticAt q.2.1).comp
        (f := fun q : ℂ × (Coeff p × CoeffPair p) => q.2.1)
        (analyticAt_fst.comp analyticAt_snd)).add analyticAt_const
    exact analyticAt_fst.prod (ha.prod (analyticAt_snd.comp analyticAt_snd))
  let U := sourceSingleRootQuotientJointDomain hp hp1 W m ∩
    {q : ℂ × (Coeff p × CoeffPair p) | q.1 ≠ ξ}
  have hU : IsOpen U := (H.joint m).1.inter
    (isOpen_ne_fun continuous_fst continuous_const)
  have htU : t ∈ U := ⟨ht,by simp [ξ]⟩
  let g : ℂ × (Coeff p × CoeffPair p) → ℂ :=
    fun q => Complex.I*sourceSingleRootQuotientJointProduct hp hp1 m (fill q)/(ξ-q.1)
  have hg : AnalyticOnNhd ℂ g U := by
    intro q hq
    have hq' : fill q ∈ sourceSingleRootQuotientJointDomain hp hp1 W m := hq.1
    exact (analyticAt_const.mul (((H.joint m).2 (fill q) hq').comp
      (f := fill) (hfill q))).div (analyticAt_const.sub analyticAt_fst)
        (sub_ne_zero.mpr hq.2.symm)
  have heq : EqOn g
      (fun q : ℂ × (Coeff p × CoeffPair p) => sourcePsiZeta hp hp1 n m q.2.1 q.2.2 q.1) U := by
    intro q hq
    let b : Coeff p := Coeff.deleteCoordinate n q.2.1+lp.single p n (ξ-(Real.pi:ℂ)*n)
    have hbn : displacedRoots b n = ξ := by
      simp only [b,displacedRoots,lp.coeFn_add,Pi.add_apply,
        Coeff.deleteCoordinate_apply_same,lp.single_apply_self,zero_add]
      ring
    calc
      g q = sourcePsiGapRegularFactor hp hp1 n m b q.2.2 q.1 := by
        change Complex.I*sourceSingleRootQuotientJointProduct hp hp1 m (q.1,(b,q.2.2))/(ξ-q.1) =
          Complex.I*sourceSingleRootQuotientJointProduct hp hp1 m (q.1,(b,q.2.2))/(displacedRoots b n-q.1)
        rw [hbn]
      _ = sourcePsiZeta hp hp1 n m b q.2.2 q.1 :=
        sourcePsiGapRegularFactor_eq_zeta hp hp1 n m hmn b q.2.2 q.1 hq.1.2
          (by rw [hbn]; exact hq.2)
      _ = sourcePsiZeta hp hp1 n m q.2.1 q.2.2 q.1 := by
        apply sourcePsiZeta_congr
        intro k hkn _
        simp only [b,lp.coeFn_add,Pi.add_apply,Coeff.deleteCoordinate_apply_other n k hkn,
          lp.single_apply_ne _ _ _ hkn,add_zero]
  exact (hg.congr hU heq) t htU

end NLS.ZakharovShabat
