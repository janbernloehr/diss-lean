import NLS.ZakharovShabat.ClassicalNLSSobolevEnergy
import NLS.Fourier.FourierNLSWeightedVelocity
import NLS.SequenceSpaces.ExponentEmbedding

/-! # Local smooth solutions with conserved mass and energy

The order-one Fourier lift gives an actual H¹ curve. The order-three
persistence theorem supplies its strong time derivative. Hence the local
solution constructed from arbitrary smooth physical data conserves energy.
-/
noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The local classical equation depends only on the curve on its closed interval. -/
theorem IsClassicalNLSTrajectoryOn.congr
    {a b : ℝ} {u v : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalNLSTrajectoryOn a b u) (he : EqOn u v (Icc a b)) :
    IsClassicalNLSTrajectoryOn a b v := by
  have hev (time : ℝ) (ht : time ∈ Ioo a b) : u =ᶠ[nhds time] v :=
    Filter.eventually_of_mem (Icc_mem_nhds ht.1 ht.2) (fun r hr => he hr)
  refine ⟨hu.continuous.congr (fun r hr => (he hr).symm),?_,?_,?_,?_⟩
  · intro time ht
    exact (hu.time_differentiable time ht).congr_of_eventuallyEq (hev time ht).symm
  · intro time ht
    rw [← he ht]
    exact hu.spatial_smooth time ht
  · intro time ht
    rw [← he ht]
    exact hu.periodic time ht
  · intro time ht x
    rw [← (hev time ht).deriv_eq,← he ⟨ht.1.le,ht.2.le⟩]
    exact hu.equation time ht x

/-- Inclusion of the order-one ℓ¹ lift into the physical Hilbert H¹ space. -/
def sobolevOneToHilbertCLM :
    WeightedCoeff (SpectralWeight.sobolev 1 (by norm_num)).toWeight 1 →L[ℂ] ScalarDomain 2 :=
  (WeightedCoeff.exponentInclusion (Weight.sobolev 1) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).comp
    (WeightedCoeff.inclusionCLM _ _ (by intro n; simp only [SpectralWeight.sobolev_apply]; exact le_rfl))

@[simp] theorem sobolevOneToHilbertCLM_apply
    (a : WeightedCoeff (SpectralWeight.sobolev 1 (by norm_num)).toWeight 1) (n : ℤ) :
    (sobolevOneToHilbertCLM a).val n = a.val n := by
  simp only [sobolevOneToHilbertCLM,ContinuousLinearMap.comp_apply,
    WeightedCoeff.exponentInclusion_apply,WeightedCoeff.inclusionCLM_apply]

/-- The H¹ inclusion retains the original pointwise physical representative. -/
theorem periodOneSobolevSynthesis_sobolevOneToHilbert
    (a : WeightedCoeff (SpectralWeight.sobolev 1 (by norm_num)).toWeight 1) (x : ℝ) :
    periodOneSobolevSynthesis (sobolevOneToHilbertCLM a) (x : AddCircle (2 : ℝ)) =
      periodOneSynthesis ((SpectralWeight.sobolev 1 (by norm_num)).toCoeff a) x := by
  have he : WeightedCoeff.sobolevToL1CLM 2 (by simp) (sobolevOneToHilbertCLM a) =
      (SpectralWeight.sobolev 1 (by norm_num)).toCoeff a := by
    ext n
    simp only [WeightedCoeff.sobolevToL1CLM_apply,sobolevOneToHilbertCLM_apply,SpectralWeight.toCoeff_apply]
  rw [periodOneSobolevSynthesis_apply,he]

/-- Arbitrary smooth periodic data produce a strong local H¹ curve with an
actual classical NLS realization and conserved physical mass and energy.
The conservation statements include both endpoints of the local interval. -/
theorem exists_local_smoothNLS_with_conservation
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    ∃ T > 0, ∃ u : ℝ → ScalarDomain 2,
      (fun x : ℝ => periodOneSobolevSynthesis (u 0) (x : AddCircle (2 : ℝ))) = f ∧
      ContinuousOn u (Icc (-T) T) ∧
      (∀ time ∈ Ioo (-T) T, DifferentiableAt ℝ u time) ∧
      IsClassicalNLSTrajectoryOn (-T) T (fun time => periodOneSobolevSynthesis (u time)) ∧
      (∀ time ∈ Icc (-T) T, classicalNLSMass (periodOneSobolevSynthesis (u time)) =
        classicalNLSMass (periodOneSobolevSynthesis (u 0))) ∧
      ∀ time ∈ Icc (-T) T, scalarSobolevEnergy (u time) = scalarSobolevEnergy (u 0) := by
  obtain ⟨T,hT,z,hz0,hz,hinit,_,hlift,hsmooth⟩ := exists_local_fourierNLS_of_smooth_periodic f hf hp
  have hi : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith,hT.le⟩
  obtain ⟨v₁,hv₁,he₁⟩ := hlift 1 (by norm_num)
  obtain ⟨v₂,hv₂,he₂⟩ := hlift 2 (by norm_num)
  have hclass := isClassicalNLSTrajectoryOn_of_fourier hz v₂ hv₂.continuous he₂
    (fun time ht => (hsmooth time ht).2)
  let u := fun time => sobolevOneToHilbertCLM (v₁ time)
  have hc : ContinuousOn u (Icc (-T) T) := sobolevOneToHilbertCLM.continuous.comp_continuousOn hv₁.continuous
  have he : EqOn (fourierNLSPhysicalCurve SpectralWeight.one z)
      (fun time => periodOneSobolevSynthesis (u time)) (Icc (-T) T) := by
    intro time ht
    apply ContinuousMap.ext
    intro x
    refine Quotient.inductionOn x (fun r => ?_)
    change periodOneSynthesis (SpectralWeight.one.toCoeff (z time)) r =
      periodOneSobolevSynthesis (sobolevOneToHilbertCLM (v₁ time)) (r : AddCircle (2 : ℝ))
    rw [periodOneSobolevSynthesis_sobolevOneToHilbert]
    congr 1
    ext n
    simpa only [SpectralWeight.toCoeff_apply] using (he₁ time ht n).symm
  have hu := hclass.congr he
  have hm : Memℓp (fun n => (Weight.sobolev (1+2) n : ℂ)*(v₁ 0).val n) 1 := by
    have hm₀ := smoothPeriodOneFourierData_all_sobolev f hf hp (1+2) (by norm_num)
    have hv0 : (v₁ 0).val = (smoothPeriodOneFourierData f hf hp).val := by
      funext n
      simpa only [hz0] using he₁ 0 hi n
    simpa only [hv0] using hm₀
  have hd (time : ℝ) (ht : time ∈ Ioo (-T) T) : DifferentiableAt ℝ u time :=
    (sobolevOneToHilbertCLM.restrictScalars ℝ).differentiableAt.comp time
      (hv₁.differentiableAt_sobolev 1 (by norm_num) 0 hi hm time ht)
  refine ⟨T,hT,u,?_,hc,hd,hu,?_,?_⟩
  · have h0 := he hi
    simpa only [h0] using hinit
  · intro time ht
    exact hu.mass_eq ht hi
  · intro time ht
    exact scalarSobolevEnergy_eq_of_local_classical u hc hd hu ht hi

end NLS.ZakharovShabat
