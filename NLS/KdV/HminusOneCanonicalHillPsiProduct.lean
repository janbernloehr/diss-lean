import NLS.KdV.HillRealEnergyProduct
import NLS.KdV.HminusOneCanonicalHillPsiRealZero

/-! At every real native H-minus-one source, the intrinsic numerator
is a nonzero scalar times its literal retained-zero product, locally
uniformly on the entire energy plane. The scalar is uniquely determined.
Its universal normalization is not asserted here. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem exists_hillHminusCanonicalPsi_product_scalar
    (n : ℕ+) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ A : ℂ, A ≠ 0 ∧ TendstoLocallyUniformlyOn
      (fun N E => A*hillEnergyDeletedPartialProduct
        (fun m => hillHminusCanonicalPsiRealZero n m q hr) n E N)
      (fun E => hillHminusCanonicalPsi n (E,q)) atTop univ := by
  have hq := real_mem_hillHminusCanonicalPsiDomain q hr
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  let u : PeriodOneRealL2 := ⟨B.parent.miuraBall.actionBall.lift q,
    B.parent.miuraBall.actionBall.lift_real q (B.subset hB).1 hr⟩
  let c := B.parent.miuraBall.actionBall.shift
  exact exists_real_hill_energy_product_scalar q hr u c
    (B.parent.miuraBall.actionBall.image q (B.subset hB).1)
    (B.parent.miuraBall.actionBall.outside q (B.subset hB).1)
    (fun E => hillHminusCanonicalPsi n (E,q))
    (hillHminusCanonicalPsi_energy_entire n q hq)
    (hillHminusCanonicalPsi_energy_ne_zero n q hq) n
    (fun m => hillHminusCanonicalPsiRealZero n m q hr)
    (fun m => hillHminusCanonicalPsiRealZero_mem_gap n m q hr)
    (fun m hm => hillHminusCanonicalPsiRealZero_is_zero n m q hr hm)
    (hillHminusCanonicalPsi_arbitrary_shift_sub_sine n q hq (c:ℂ))

def hillHminusPsiProductScalar (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : ℂ :=
  Classical.choose (exists_hillHminusCanonicalPsi_product_scalar n q hr)

theorem hillHminusPsiProductScalar_ne_zero (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : hillHminusPsiProductScalar n q hr ≠ 0 :=
  (Classical.choose_spec (exists_hillHminusCanonicalPsi_product_scalar n q hr)).1

theorem hillHminusCanonicalPsi_product_convergence (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : TendstoLocallyUniformlyOn
      (fun N E => hillHminusPsiProductScalar n q hr*hillEnergyDeletedPartialProduct
        (fun m => hillHminusCanonicalPsiRealZero n m q hr) n E N)
      (fun E => hillHminusCanonicalPsi n (E,q)) atTop univ :=
  (Classical.choose_spec (exists_hillHminusCanonicalPsi_product_scalar n q hr)).2

theorem hillHminusPsiProductScalar_unique (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (A : ℂ)
    (hA : TendstoLocallyUniformlyOn
      (fun N E => A*hillEnergyDeletedPartialProduct
        (fun m => hillHminusCanonicalPsiRealZero n m q hr) n E N)
      (fun E => hillHminusCanonicalPsi n (E,q)) atTop univ) :
    A = hillHminusPsiProductScalar n q hr := by
  exact const_product_scalar_unique
    (fun N E => hillEnergyDeletedPartialProduct
      (fun m => hillHminusCanonicalPsiRealZero n m q hr) n E N)
    (fun E => hillHminusCanonicalPsi n (E,q))
    (hillHminusCanonicalPsi_energy_ne_zero n q (real_mem_hillHminusCanonicalPsiDomain q hr))
    A (hillHminusPsiProductScalar n q hr)
    (fun E => hA.tendsto_at (mem_univ E))
    (fun E => (hillHminusCanonicalPsi_product_convergence n q hr).tendsto_at (mem_univ E))

theorem hillHminusCanonicalPsi_product_deriv_convergence (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : TendstoLocallyUniformlyOn
      (fun N => deriv (fun E => hillHminusPsiProductScalar n q hr*hillEnergyDeletedPartialProduct
        (fun m => hillHminusCanonicalPsiRealZero n m q hr) n E N))
      (deriv (fun E => hillHminusCanonicalPsi n (E,q))) atTop univ := by
  apply (hillHminusCanonicalPsi_product_convergence n q hr).deriv _ isOpen_univ
  apply Eventually.of_forall
  intro N E _
  exact (analyticAt_const.mul (analyticOnNhd_hillEnergyDeletedPartialProduct
    (fun m => hillHminusCanonicalPsiRealZero n m q hr) n N E (mem_univ E))).differentiableAt.differentiableWithinAt

end NLS.KdV
