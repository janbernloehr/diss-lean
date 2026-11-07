import NLS.KdV.HillMiuraMeanNormalization
import NLS.SequenceSpaces.PeriodOneMiuraBoundedCompactness

/-! Every original physical real mean-zero Hminus source has an actual
real L2 Riccati lift of MINIMAL energy shift. Bounded slices of the full
real lift family are compact in the STRONG original L2 norm. This does
not yet assert that a minimizing lift has zero mean. -/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ComplexConjugate
namespace NLS.KdV

/-- All real L2 lifts with the exact energy shift forced by the zero mode. -/
def hillRealMiuraLiftSet (q : HillRealMeanZeroSource) : Set (Coeff 2) :=
  {u | (∀ k : ℤ, u (-k)=conj (u k)) ∧
    periodOneMiura u=hillRealMeanZeroInclusion q+
      periodOneL2Inclusion (lp.single 2 0 ((‖u‖^2:ℝ):ℂ))}

private theorem continuous_miura_norm_shift :
    Continuous (fun u : Coeff 2 => periodOneL2Inclusion (lp.single 2 0 ((‖u‖^2:ℝ):ℂ))) :=
  periodOneL2Inclusion.continuous.comp
    ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp
      (continuous_ofReal.comp (continuous_norm.pow 2)))

theorem isClosed_hillRealMiuraLiftSet (q : HillRealMeanZeroSource) :
    IsClosed (hillRealMiuraLiftSet q) := by
  have hr : IsClosed {u : Coeff 2 | ∀ k : ℤ, u (-k)=conj (u k)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun k => isClosed_eq
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (-k)).continuous
      (continuous_conj.comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).continuous))
  exact hr.inter (isClosed_eq continuous_periodOneMiura
    (continuous_const.add continuous_miura_norm_shift))

/-- Real lift families are compact after an L2 bound, in the strong norm. -/
theorem isCompact_hillRealMiuraLiftSet_inter_closedBall (q : HillRealMeanZeroSource)
    (B : ℝ) (hB : 0 ≤ B) :
    IsCompact (hillRealMiuraLiftSet q ∩ closedBall (0 : Coeff 2) B) := by
  let f : ℝ → PeriodOneHminusOne := fun c => hillRealMeanZeroInclusion q+
    periodOneL2Inclusion (lp.single 2 0 (c:ℂ))
  have hf : Continuous f := continuous_const.add (periodOneL2Inclusion.continuous.comp
    ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp continuous_ofReal))
  have hK : IsCompact (f '' Icc 0 (B^2)) := isCompact_Icc.image hf
  apply (isCompact_periodOneMiura_preimage_inter_closedBall _ hK B).of_isClosed_subset
    ((isClosed_hillRealMiuraLiftSet q).inter isClosed_closedBall)
  intro u hu
  have hn : ‖u‖ ≤ B := by simpa only [mem_closedBall,dist_zero_right] using hu.2
  refine ⟨?_,hu.2⟩
  refine ⟨‖u‖^2,⟨sq_nonneg _,by nlinarith [norm_nonneg u]⟩,?_⟩
  exact hu.1.2.symm

/-- Large real shifted charts already give surjectivity when the lift
mean is unrestricted. The zero-mean lift assertion is separate. -/
theorem surjective_hillRealNormalizedMiura : Function.Surjective hillRealNormalizedMiura := by
  intro q
  obtain ⟨c,_,_,V,_,hqV,u,_,hreal,hi⟩ :=
    exists_real_periodOneMiura_energyChart (hillRealMeanZeroInclusion q) q.property 0
  let v : PeriodOneRealL2 := ⟨u (hillRealMeanZeroInclusion q),hreal⟩
  refine ⟨v,hillRealNormalizedMiura_eq_of_shifted_image q v (c^2) ?_⟩
  simpa only [Complex.ofReal_pow] using hi (hillRealMeanZeroInclusion q) hqV

/-- A genuine real lift exists and minimizes its original L2 norm among
ALL genuine real lifts, without any small-ball or cutoff restriction. -/
theorem exists_minimal_real_Miura_lift (q : HillRealMeanZeroSource) :
    ∃ u : PeriodOneRealL2, hillRealNormalizedMiura u=q ∧
      ∀ v : PeriodOneRealL2, hillRealNormalizedMiura v=q → ‖u.val‖ ≤ ‖v.val‖ := by
  obtain ⟨u₀,hu₀⟩ := surjective_hillRealNormalizedMiura q
  have h₀ : u₀.val ∈ hillRealMiuraLiftSet q := by
    refine ⟨u₀.property,?_⟩
    rw [← hu₀]
    exact hillRealNormalizedMiura_image u₀
  have hne : (hillRealMiuraLiftSet q ∩ closedBall (0 : Coeff 2) ‖u₀.val‖).Nonempty :=
    ⟨u₀.val,h₀,by simp⟩
  obtain ⟨u,hu,hmin⟩ := (isCompact_hillRealMiuraLiftSet_inter_closedBall q ‖u₀.val‖ (norm_nonneg _)).exists_isMinOn
    (f := fun a : Coeff 2 => ‖a‖) hne continuous_norm.continuousOn
  let v : PeriodOneRealL2 := ⟨u,hu.1.1⟩
  have hv : hillRealNormalizedMiura v=q :=
    hillRealNormalizedMiura_eq_of_shifted_image q v (‖u‖^2) hu.1.2
  refine ⟨v,hv,?_⟩
  intro w hw
  have hwL : w.val ∈ hillRealMiuraLiftSet q := by
    refine ⟨w.property,?_⟩
    rw [← hw]
    exact hillRealNormalizedMiura_image w
  by_cases hn : ‖w.val‖ ≤ ‖u₀.val‖
  · exact hmin ⟨hwL,by simpa only [mem_closedBall,dist_zero_right] using hn⟩
  · have huB : ‖u‖ ≤ ‖u₀.val‖ := by simpa only [mem_closedBall,dist_zero_right] using hu.2
    exact huB.trans (le_of_not_ge hn)

/-- The minimal energy shift is attained among all actual real shifted lifts. -/
theorem exists_minimal_real_Miura_energy_shift (q : HillRealMeanZeroSource) :
    ∃ u : PeriodOneRealL2, ∃ c : ℝ, 0 ≤ c ∧
      periodOneMiura u.val=hillRealMeanZeroInclusion q+
        periodOneL2Inclusion (lp.single 2 0 (c:ℂ)) ∧
      ∀ v : PeriodOneRealL2, ∀ d : ℝ,
        periodOneMiura v.val=hillRealMeanZeroInclusion q+
          periodOneL2Inclusion (lp.single 2 0 (d:ℂ)) → c ≤ d := by
  obtain ⟨u,hu,hmin⟩ := exists_minimal_real_Miura_lift q
  refine ⟨u,‖u.val‖^2,sq_nonneg _,?_,?_⟩
  · rw [← hu]
    exact hillRealNormalizedMiura_image u
  · intro v d hv
    have hnorm := hmin v (hillRealNormalizedMiura_eq_of_shifted_image q v d hv)
    rw [hillMiura_shift_eq_norm_sq q v d hv]
    nlinarith [norm_nonneg u.val,norm_nonneg v.val]

end NLS.KdV
