import NLS.KdV.HillCanonicalComplexProductScalar

/-! The ACTUAL analytic complex scalar normalizes the SAME literal
finite Hill cutoffs to the intrinsic numerator, locally uniformly in
joint energy/source inputs. At each complex source their energy
derivatives converge locally uniformly on the ENTIRE energy plane. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillHminusCanonicalPsi_complex_product_convergence (n : ℕ+) :
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) (t : ℂ × PeriodOneHminusOne) => hillHminusCanonicalPsiProductScalar n t.2*
        hillEnergySequencePartialProduct n N (t.1,hillHminusCanonicalZeroSequence n t.2))
      (hillHminusCanonicalPsi n) atTop (univ ×ˢ hillHminusCanonicalZeroSequenceDomain) := by
  let A : ℂ × PeriodOneHminusOne → ℂ := fun t => hillHminusCanonicalPsiProductScalar n t.2
  have hA : AnalyticOnNhd ℂ A (univ ×ˢ hillHminusCanonicalZeroSequenceDomain) := by
    intro t ht
    exact (analyticOnNhd_hillHminusCanonicalPsiProductScalar n t.2 ht.2).comp analyticAt_snd
  have h := (tendstoLocallyUniformlyOn_const_family A _).mul₀
    (tendstoLocallyUniformlyOn_hillHminusCanonicalZeroProduct n) hA.continuousOn
    (analyticOnNhd_hillHminusCanonicalZeroProduct n).continuousOn
  apply h.congr_right
  intro t ht
  exact (hillHminusCanonicalPsi_eq_complex_scalar_mul_product n t.2 ht.2 t.1).symm

theorem hillHminusCanonicalPsi_complex_product_energy_convergence (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalZeroSequenceDomain) :
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) (E : ℂ) => hillHminusCanonicalPsiProductScalar n q*
        hillEnergySequencePartialProduct n N (E,hillHminusCanonicalZeroSequence n q))
      (fun E => hillHminusCanonicalPsi n (E,q)) atTop univ :=
  (hillHminusCanonicalPsi_complex_product_convergence n).comp (fun E : ℂ => (E,q))
    (fun _ _ => ⟨mem_univ _,hq⟩) (continuous_id.prodMk continuous_const).continuousOn

theorem analyticAt_hillEnergySequencePartialProduct (n : ℕ+) (N : ℕ)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : AnalyticAt ℂ (hillEnergySequencePartialProduct n N) t := by
  have he : hillEnergySequencePartialProduct n N = fun s => jointDeletedSingleSpectralPartialProduct 0 N (0,hillEnergyProductEmbedding n s) :=
    funext (hillEnergySequencePartialProduct_eq_embedding n N)
  rw [he]
  exact (analyticOnNhd_jointDeletedSingleSpectralPartialProduct 0 N _ (mem_univ _)).comp
    (analyticAt_const.prod (analyticAt_hillEnergyProductEmbedding n t))

theorem hillHminusCanonicalPsi_complex_product_deriv_convergence (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalZeroSequenceDomain) :
    TendstoLocallyUniformlyOn
      (fun N => deriv (fun E : ℂ => hillHminusCanonicalPsiProductScalar n q*
        hillEnergySequencePartialProduct n N (E,hillHminusCanonicalZeroSequence n q)))
      (deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,q))) atTop univ := by
  apply (hillHminusCanonicalPsi_complex_product_energy_convergence n q hq).deriv _ isOpen_univ
  apply Eventually.of_forall
  intro N E _
  exact (analyticAt_const.mul ((analyticAt_hillEnergySequencePartialProduct n N _).comp
    (f := fun w : ℂ => (w,hillHminusCanonicalZeroSequence n q)) (analyticAt_id.prod analyticAt_const))).differentiableAt.differentiableWithinAt

theorem hillHminusCanonicalPsi_energy_deriv_eq_scalar_mul_product (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalZeroSequenceDomain) (E : ℂ) :
    deriv (fun z : ℂ => hillHminusCanonicalPsi n (z,q)) E =
      hillHminusCanonicalPsiProductScalar n q*deriv (fun z : ℂ => hillHminusCanonicalZeroProduct n (z,q)) E := by
  have hP := (analyticOnNhd_hillHminusCanonicalZeroProduct n (E,q) ⟨mem_univ _,hq⟩).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)
  have h := hP.differentiableAt.hasDerivAt.const_mul (hillHminusCanonicalPsiProductScalar n q)
  have he : (fun z : ℂ => hillHminusCanonicalPsi n (z,q)) =
      (fun z => hillHminusCanonicalPsiProductScalar n q*hillHminusCanonicalZeroProduct n (z,q)) :=
    funext (hillHminusCanonicalPsi_eq_complex_scalar_mul_product n q hq)
  rw [he]
  exact h.deriv

end NLS.KdV
