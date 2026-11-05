import NLS.KdV.HillDiscriminantCoefficientContinuity
import NLS.KdV.HillIsospectralData
import NLS.SequenceSpaces.WeightedCoefficientCompactness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Every bounded sequence of actual real period-one rough Hill sources
has a raw coefficientwise convergent subsequence in the same physical space. -/
theorem exists_hillRealSource_coefficientwise_subseq
    (a : ℕ → RealPeriodOneHillPotential)
    (hb : Bornology.IsBounded (range (fun k => (a k).val))) :
    ∃ b : RealPeriodOneHillPotential, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ n : ℤ, Tendsto (fun k => (a (σ k)).val.val n) atTop (𝓝 (b.val.val n)) := by
  obtain ⟨b,σ,hσ,ht⟩ := WeightedCoeff.exists_coefficientwise_tendsto_subseq_of_bounded
    SpectralWeight.one.toWeight (fun k => (a k).val) hb
  have heven : SpectralWeight.one.toCoeff b∈Coeff.paritySubspace 0 := by
    rw [Coeff.mem_paritySubspace]
    intro n hn
    simp only [SpectralWeight.toCoeff_apply]
    have hz (k : ℕ) : (a (σ k)).val.val n=0 := by
      simpa only [SpectralWeight.toCoeff_apply] using
        (Coeff.mem_paritySubspace 0 _).mp (a (σ k)).property.1 n hn
    exact tendsto_nhds_unique (ht n) (by simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))
  have hreal : IsRealHillPotential (SpectralWeight.one.toCoeff b) := by
    intro n
    simp only [SpectralWeight.toCoeff_apply]
    have hc := Complex.continuous_conj.continuousAt.tendsto.comp (ht n)
    have he (k : ℕ) : conj ((a (σ k)).val.val n)=(a (σ k)).val.val (-n) := by
      simpa only [SpectralWeight.toCoeff_apply] using ((a (σ k)).property.2 n).symm
    exact tendsto_nhds_unique (ht (-n)) (hc.congr' (Filter.Eventually.of_forall he))
  exact ⟨⟨b,heven,hreal⟩,σ,hσ,ht⟩

/-- Actual mean-zero isospectral Hill sources are sequentially compact in
the original rough source norm. Boundedness and absence of norm loss are
proved from the actual discriminant and quadratic action trace. -/
theorem exists_hillMeanZeroIsospectral_tendsto_subseq
    (q : RealPeriodOneHillPotential) (hq : q.val.val 0=0)
    (a : ℕ → RealPeriodOneHillPotential) (hmean : ∀ k, (a k).val.val 0=0)
    (hiso : ∀ k, ∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff (a k).val) E=
      hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E) :
    ∃ b : RealPeriodOneHillPotential, b.val.val 0=0 ∧
      (∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff b.val) E=
        hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E) ∧
      ‖b.val‖=‖q.val‖ ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun k => (a (σ k)).val) atTop (𝓝 b.val) := by
  have hnorm (k : ℕ) : ‖(a k).val‖=‖q.val‖ :=
    hillSource_norm_eq_of_discriminant_eq (a k) q (hmean k) hq (hiso k)
  have hb : Bornology.IsBounded (range (fun k => (a k).val)) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨‖q.val‖,by rintro _ ⟨k,rfl⟩; exact (hnorm k).le⟩
  obtain ⟨b,σ,hσ,ht⟩ := exists_hillRealSource_coefficientwise_subseq a hb
  have hbmean : b.val.val 0=0 := tendsto_nhds_unique (ht 0) (by
    simpa only [hmean] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))
  have hbc : Bornology.IsBounded (range (fun k => SpectralWeight.one.toCoeff (a (σ k)).val)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨‖q.val‖,?_⟩
    rintro _ ⟨k,rfl⟩
    exact (SpectralWeight.norm_toCoeff_le _ _).trans_eq (hnorm (σ k))
  have hbiso (E : ℂ) : hillL2Discriminant (SpectralWeight.one.toCoeff b.val) E=
      hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E := by
    have hd := tendsto_hillDiscriminant_of_bounded_coefficientwise
      (fun k => SpectralWeight.one.toCoeff (a (σ k)).val) (SpectralWeight.one.toCoeff b.val)
      hbc (by simpa only [SpectralWeight.toCoeff_apply] using ht) E
    exact tendsto_nhds_unique hd (by
      simpa only [hiso] using (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E) atTop
        (𝓝 (hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E))))
  have hbnorm : ‖b.val‖=‖q.val‖ := hillSource_norm_eq_of_discriminant_eq b q hbmean hq hbiso
  refine ⟨b,hbmean,hbiso,hbnorm,σ,hσ,?_⟩
  apply WeightedCoeff.tendsto_of_coefficientwise_of_norm_sq SpectralWeight.one.toWeight
    (fun k => (a (σ k)).val) b.val ht
  simpa only [hnorm,hbnorm] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖q.val‖^2) atTop (𝓝 (‖q.val‖^2)))

end NLS.KdV
