import NLS.KdV.HillEnergySequenceProduct
import NLS.KdV.HminusOneCanonicalHillPsiProduct
import NLS.KdV.HminusOneHillPsiZeroSequenceContinuity

/-! The actual real-source literal Hill product is jointly continuous
in energy and source. Its unique nonzero normalization scalar is
continuous in the original native source norm. Its universal value is
not inferred from continuity or the free value. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillEnergySequencePartialProduct_realZero (n : ℕ+) (N : ℕ) (E : ℂ)
    (q : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a}) :
    hillEnergySequencePartialProduct n N (E,hillHminusPsiZeroDisplacement n q) =
      hillEnergyDeletedPartialProduct (fun m => hillHminusCanonicalPsiRealZero n m q.val q.property) n E N := by
  unfold hillEnergySequencePartialProduct hillEnergyDeletedPartialProduct
  apply Finset.prod_congr rfl
  intro j _
  let m : ℕ+ := ⟨j+1,by omega⟩
  change (((Real.pi:ℂ)*((j:ℂ)+1))^2+((j:ℂ)+1)*
    (((hillHminusCanonicalPsiRealZero n m q.val q.property:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ))-E)/
      ((Real.pi:ℂ)*((j:ℂ)+1))^2 =
    ((hillHminusCanonicalPsiRealZero n m q.val q.property:ℂ)-E)/((Real.pi:ℂ)*((j:ℂ)+1))^2
  have hcast : ((m:ℕ):ℂ) = (j:ℂ)+1 := by change ((j+1:ℕ):ℂ) = (j:ℂ)+1; push_cast; rfl
  rw [hcast]
  have hd : (j:ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero j
  field_simp
  ring

def hillHminusPsiLiteralProduct (n : ℕ+)
    (t : ℂ × {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a}) : ℂ :=
  hillEnergySequenceProduct n (t.1,hillHminusPsiZeroDisplacement n t.2)

theorem continuous_hillHminusPsiLiteralProduct (n : ℕ+) : Continuous (hillHminusPsiLiteralProduct n) := by
  have hprod : Continuous (hillEnergySequenceProduct n) :=
    continuous_iff_continuousAt.mpr (fun t => (analyticAt_hillEnergySequenceProduct n t).continuousAt)
  exact hprod.comp (continuous_fst.prodMk ((continuous_hillHminusPsiZeroDisplacement n).comp continuous_snd))

theorem hillHminusCanonicalPsi_eq_scalar_mul_literalProduct (n : ℕ+) (E : ℂ)
    (q : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a}) :
    hillHminusCanonicalPsi n (E,q.val) =
      hillHminusPsiProductScalar n q.val q.property*hillHminusPsiLiteralProduct n (E,q) := by
  have hlim := (tendsto_hillEnergySequencePartialProduct n (E,hillHminusPsiZeroDisplacement n q)).const_mul
    (hillHminusPsiProductScalar n q.val q.property)
  simp_rw [hillEnergySequencePartialProduct_realZero] at hlim
  exact tendsto_nhds_unique
    ((hillHminusCanonicalPsi_product_convergence n q.val q.property).tendsto_at (mem_univ E)) hlim

theorem continuousAt_hillHminusPsiProductScalar (n : ℕ+)
    (q : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a}) :
    ContinuousAt (fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} =>
      hillHminusPsiProductScalar n a.val a.property) q := by
  have hne := hillHminusCanonicalPsi_energy_ne_zero n q.val
    (real_mem_hillHminusCanonicalPsiDomain q.val q.property)
  obtain ⟨E,hE⟩ : ∃ E : ℂ, hillHminusCanonicalPsi n (E,q.val) ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hprod : Continuous (fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} =>
      hillHminusPsiLiteralProduct n (E,a)) :=
    (continuous_hillHminusPsiLiteralProduct n).comp (continuous_const.prodMk continuous_id)
  have hpnz : hillHminusPsiLiteralProduct n (E,q) ≠ 0 := by
    intro hz
    exact hE (by rw [hillHminusCanonicalPsi_eq_scalar_mul_literalProduct n E q,hz,mul_zero])
  have hP : ContinuousAt (fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} =>
      hillHminusCanonicalPsi n (E,a.val)) q :=
    (analyticOnNhd_hillHminusCanonicalPsi n (E,q.val)
      ⟨mem_univ _,real_mem_hillHminusCanonicalPsiDomain q.val q.property⟩).continuousAt.comp
      (f := fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} => (E,a.val))
      (continuous_const.prodMk continuous_subtype_val).continuousAt
  apply (hP.div hprod.continuousAt hpnz).congr_of_eventuallyEq
  filter_upwards [hprod.continuousAt.eventually_ne hpnz] with a ha
  exact (eq_div_iff ha).mpr (hillHminusCanonicalPsi_eq_scalar_mul_literalProduct n E a).symm

theorem continuous_hillHminusPsiProductScalar (n : ℕ+) :
    Continuous (fun q : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a} =>
      hillHminusPsiProductScalar n q.val q.property) :=
  continuous_iff_continuousAt.mpr (continuousAt_hillHminusPsiProductScalar n)

end NLS.KdV
