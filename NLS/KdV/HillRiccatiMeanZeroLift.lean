import NLS.KdV.HillRiccatiMinimum
import NLS.KdV.HillMiuraRealLocalInverse

/-! A minimal real Riccati lift has zero mean: otherwise the actual
real-preserving Miura inverse lowers its energy shift. This constructs a
mean-zero real L2 lift for EVERY original rough physical source, without
a ground-state positivity or unverified Riccati-surjectivity assumption. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

theorem mean_zero_of_minimal_real_Miura_energy_shift
    (q : HillRealMeanZeroSource) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val=hillRealMeanZeroInclusion q+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hmin : ∀ v : PeriodOneRealL2, ∀ d : ℝ,
      periodOneMiura v.val=hillRealMeanZeroInclusion q+
        periodOneL2Inclusion (lp.single 2 0 (d:ℂ)) → c ≤ d) : u.val 0=0 := by
  by_contra hu
  obtain ⟨g,_,_,_,hright,hreal⟩ := exists_real_preserving_localInverse_periodOneMiura u hu
  let C : ℂ →L[ℂ] PeriodOneHminusOne := periodOneL2Inclusion.comp
    (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0)
  let p : ℝ → PeriodOneHminusOne := fun t => periodOneMiura u.val+C (t:ℂ)
  have hp : Tendsto p (𝓝 0) (𝓝 (periodOneMiura u.val)) := by
    have hc : Continuous p := continuous_const.add (C.continuous.comp continuous_ofReal)
    simpa only [p,Complex.ofReal_zero,map_zero,add_zero] using hc.continuousAt.tendsto (x := 0)
  have himage (t : ℝ) : p t=hillRealMeanZeroInclusion q+C ((c+t:ℝ):ℂ) := by
    change periodOneMiura u.val+C (t:ℂ)=hillRealMeanZeroInclusion q+C ((c+t:ℝ):ℂ)
    change periodOneMiura u.val=hillRealMeanZeroInclusion q+C (c:ℂ) at hi
    rw [hi,Complex.ofReal_add,map_add,add_assoc]
  have hpr (t : ℝ) : IsRealPeriodOneHminusOne (p t) := by
    rw [himage]
    have hC : IsRealPeriodOneHminusOne (C ((c+t:ℝ):ℂ)) :=
      periodOneL2Inclusion_single_zero_real (c+t)
    intro k
    change (hillRealMeanZeroInclusion q).val (-k)+(C ((c+t:ℝ):ℂ)).val (-k)=
      conj ((hillRealMeanZeroInclusion q).val k+(C ((c+t:ℝ):ℂ)).val k)
    have hq : IsRealPeriodOneHminusOne (hillRealMeanZeroInclusion q) := q.property
    rw [hq k,hC k,map_add]
  have he : ∀ᶠ t in 𝓝 (0:ℝ), periodOneMiura (g (p t))=p t ∧
      ∀ k : ℤ, g (p t) (-k)=conj (g (p t) k) := by
    filter_upwards [hp.eventually hright,hp.eventually hreal] with t ht hr
    exact ⟨ht,hr (hpr t)⟩
  obtain ⟨δ,hδ,hδp⟩ := Metric.eventually_nhds_iff.mp he
  have ht : dist (-δ/2) (0:ℝ) < δ := by
    rw [dist_zero_right,Real.norm_eq_abs,abs_of_neg (by linarith)]
    linarith
  obtain ⟨hsolve,hv⟩ := hδp ht
  let v : PeriodOneRealL2 := ⟨g (p (-δ/2)),hv⟩
  have hvimage : periodOneMiura v.val=hillRealMeanZeroInclusion q+
      periodOneL2Inclusion (lp.single 2 0 ((c+(-δ/2):ℝ):ℂ)) :=
    hsolve.trans (himage (-δ/2))
  have hle := hmin v (c+(-δ/2)) hvimage
  linarith

/-- Every original physical real mean-zero Hminus source has a genuine
real mean-zero L2 Riccati lift with the EXACT original energy translation. -/
theorem exists_mean_zero_real_Miura_lift (q : HillRealMeanZeroSource) :
    ∃ u : PeriodOneRealL2, u.val 0=0 ∧
      periodOneMiura u.val=hillRealMeanZeroInclusion q+
        periodOneL2Inclusion (lp.single 2 0 ((‖u.val‖^2:ℝ):ℂ)) := by
  obtain ⟨u,c,_,hi,hmin⟩ := exists_minimal_real_Miura_energy_shift q
  refine ⟨u,mean_zero_of_minimal_real_Miura_energy_shift q u c hi hmin,?_⟩
  rwa [hillMiura_shift_eq_norm_sq q u c hi] at hi

/-- The explicit normalized rough Miura map is onto even after restricting
to genuine physical real lifts with zero Fourier mean. -/
theorem surjective_hillRealNormalizedMiura_mean_zero (q : HillRealMeanZeroSource) :
    ∃ u : PeriodOneRealL2, u.val 0=0 ∧ hillRealNormalizedMiura u=q := by
  obtain ⟨u,hu,hi⟩ := exists_mean_zero_real_Miura_lift q
  exact ⟨u,hu,hillRealNormalizedMiura_eq_of_shifted_image q u (‖u.val‖^2) hi⟩

end NLS.KdV
