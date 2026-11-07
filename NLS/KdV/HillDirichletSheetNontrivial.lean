import NLS.KdV.HillNativeDirichletSheetFirstVariation
import NLS.ComplexAnalysis.AnalyticProductCancellation

/-! The actual prescribed sheet is not identically zero at any
positive index. Its independently verified free derivative supplies
the nontriviality needed for analytic cancellation through closed gaps. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

theorem exists_hillHminusDirichletSheet_ne_zero (n : ℕ+) :
    ∃ q ∈ hillHminusCanonicalDirichletDomain, hillHminusDirichletSheet n q ≠ 0 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have h0 := real_mem_hillHminusCanonicalDirichletDomain 0 hr
  let h : PeriodOneHminusOne := WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (n:ℤ) 1)
  have hn : h.val (n:ℤ)=1 := by simp [h,WeightedCoeff.ofFinsupp_apply]
  have hm : h.val (-(n:ℤ))=0 := by simp [h,WeightedCoeff.ofFinsupp_apply]
  have hval : (fderiv ℂ (hillHminusDirichletSheet n) 0) h=
      (-1:ℂ)^(n:ℕ)/(2*I*((Real.pi:ℂ)*n)) := by
    rw [fderiv_hillHminusDirichletSheet_zero_apply,hn,hm,sub_zero,mul_one]
  have hc : (-1:ℂ)^(n:ℕ)/(2*I*((Real.pi:ℂ)*n)) ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (by norm_num)) (by simp [Real.pi_ne_zero,n.ne_zero])
  by_contra he
  push Not at he
  have hlocal : hillHminusDirichletSheet n =ᶠ[𝓝 (0 : PeriodOneHminusOne)] (fun _ => 0) := by
    filter_upwards [isOpen_hillHminusCanonicalDirichletDomain.mem_nhds h0] with q hq
    exact he q hq
  have hz : (fderiv ℂ (hillHminusDirichletSheet n) 0) h=0 := by
    rw [hlocal.fderiv_eq]
    simp
  exact hc (hval.symm.trans hz)

end NLS.KdV
