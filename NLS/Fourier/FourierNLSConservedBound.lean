import NLS.ZakharovShabat.ScalarNLSConservedBound
import NLS.ZakharovShabat.LocalSmoothNLSConservation

/-! # A uniform conserved bound on every smooth reference interval -/
noncomputable section
open Set NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.Fourier

/-- Unit-weight inclusion retains the norm exactly. -/
@[simp] theorem norm_one_toCoeff (a : WeightedCoeff SpectralWeight.one.toWeight 1) :
    ‖SpectralWeight.one.toCoeff a‖ = ‖a‖ := by
  have he : SpectralWeight.one.toCoeff a = WeightedCoeff.weightEquiv SpectralWeight.one.toWeight 1 a := by
    ext n
    simp only [SpectralWeight.toCoeff_apply,WeightedCoeff.weightEquiv_apply,
      SpectralWeight.one_apply,Complex.ofReal_one,one_mul]
  rw [he]
  rfl

/-- All initial Sobolev orders make any reference trajectory a physical
classical solution on its whole closed interval. -/
theorem IsFourierNLSTrajectoryOn.isClassical_physical_of_all_sobolev
    {a b : ℝ} {z : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1}
    (hz : IsFourierNLSTrajectoryOn SpectralWeight.one a b z)
    (initial : ℝ) (hi : initial ∈ Icc a b)
    (hall : ∀ s : ℝ, 0 ≤ s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*(z initial).val n) 1) :
    IsClassicalNLSTrajectoryOn a b (fourierNLSPhysicalCurve SpectralWeight.one z) := by
  obtain ⟨v,hv,he⟩ := hz.exists_sobolev_lift initial hi 2 (by norm_num) (hall 2 (by norm_num))
  exact isClassicalNLSTrajectoryOn_of_fourier hz v hv.continuous he
    (hz.contDiff_synthesis_of_all_sobolev initial hi hall)

/-- Every smooth reference trajectory admits a coefficient-identical strong
H¹ realization conserving mass and energy on the same closed interval. -/
theorem IsFourierNLSTrajectoryOn.exists_conserved_hilbert_lift
    {a b : ℝ} {z : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1}
    (hz : IsFourierNLSTrajectoryOn SpectralWeight.one a b z)
    (initial : ℝ) (hi : initial ∈ Icc a b)
    (hall : ∀ s : ℝ, 0 ≤ s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*(z initial).val n) 1) :
    ∃ u : ℝ → ScalarDomain 2,
      ContinuousOn u (Icc a b) ∧
      (∀ time ∈ Icc a b, ∀ n : ℤ, (u time).val n = (z time).val n) ∧
      (∀ time ∈ Ioo a b, DifferentiableAt ℝ u time) ∧
      IsClassicalNLSTrajectoryOn a b (fun time => periodOneSobolevSynthesis (u time)) ∧
      (∀ time ∈ Icc a b, classicalNLSMass (periodOneSobolevSynthesis (u time)) =
        classicalNLSMass (periodOneSobolevSynthesis (u initial))) ∧
      ∀ time ∈ Icc a b, scalarSobolevEnergy (u time) = scalarSobolevEnergy (u initial) := by
  obtain ⟨v,hv,he⟩ := hz.exists_sobolev_lift initial hi 1 (by norm_num) (hall 1 (by norm_num))
  let u := fun time => sobolevOneToHilbertCLM (v time)
  have hc : ContinuousOn u (Icc a b) := sobolevOneToHilbertCLM.continuous.comp_continuousOn hv.continuous
  have heq (time : ℝ) (ht : time ∈ Icc a b) (n : ℤ) : (u time).val n = (z time).val n := by
    change (sobolevOneToHilbertCLM (v time)).val n = _
    rw [sobolevOneToHilbertCLM_apply,he time ht n]
  have hp : EqOn (fourierNLSPhysicalCurve SpectralWeight.one z)
      (fun time => periodOneSobolevSynthesis (u time)) (Icc a b) := by
    intro time ht
    apply ContinuousMap.ext
    intro x
    refine Quotient.inductionOn x (fun r => ?_)
    change periodOneSynthesis (SpectralWeight.one.toCoeff (z time)) r =
      periodOneSobolevSynthesis (sobolevOneToHilbertCLM (v time)) (r : AddCircle (2 : ℝ))
    rw [periodOneSobolevSynthesis_sobolevOneToHilbert]
    congr 1
    ext n
    simpa only [SpectralWeight.toCoeff_apply] using (he time ht n).symm
  have hu := (hz.isClassical_physical_of_all_sobolev initial hi hall).congr hp
  have hm : Memℓp (fun n => (Weight.sobolev (1+2) n : ℂ)*(v initial).val n) 1 := by
    simpa only [he initial hi] using hall (1+2) (by norm_num)
  have hd (time : ℝ) (ht : time ∈ Ioo a b) : DifferentiableAt ℝ u time :=
    (sobolevOneToHilbertCLM.restrictScalars ℝ).differentiableAt.comp time
      (hv.differentiableAt_sobolev 1 (by norm_num) initial hi hm time ht)
  exact ⟨u,hc,heq,hd,hu,fun time ht => hu.mass_eq ht hi,
    fun time ht => scalarSobolevEnergy_eq_of_local_classical u hc hd hu ht hi⟩

/-- The original ℓ¹ norm is bounded solely by the physical mass and energy
of coefficient-identical H¹ initial data, independent of the interval length. -/
theorem IsFourierNLSTrajectoryOn.norm_le_conserved
    {a b : ℝ} {z : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1}
    (hz : IsFourierNLSTrajectoryOn SpectralWeight.one a b z)
    (initial : ℝ) (hi : initial ∈ Icc a b)
    (hall : ∀ s : ℝ, 0 ≤ s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*(z initial).val n) 1)
    (u₀ : ScalarDomain 2) (h₀ : ∀ n : ℤ, u₀.val n = (z initial).val n)
    (time : ℝ) (ht : time ∈ Icc a b) : ‖z time‖ ≤ nlsConservedBound u₀ := by
  obtain ⟨u,_,he,_,_,hm,hE⟩ := hz.exists_conserved_hilbert_lift initial hi hall
  have hu₀ : u initial = u₀ := by
    apply Subtype.ext
    funext n
    exact (he initial hi n).trans (h₀ n).symm
  have heq : SpectralWeight.one.toCoeff (z time) = WeightedCoeff.sobolevToL1CLM 2 (by simp) (u time) := by
    ext n
    simpa only [SpectralWeight.toCoeff_apply,WeightedCoeff.sobolevToL1CLM_apply] using (he time ht n).symm
  rw [← norm_one_toCoeff,heq]
  calc
    _ ≤ nlsConservedBound (u time) := norm_sobolevToL1_le_conserved _
    _ = nlsConservedBound (u initial) := nlsConservedBound_eq_of_conservation _ _ (hm time ht) (hE time ht)
    _ = _ := by rw [hu₀]

/-- Canonical H¹ initial data constructed from the original weighted ℓ¹ membership. -/
def fourierNLSHilbertData (z : WeightedCoeff SpectralWeight.one.toWeight 1)
    (hm : Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*z.val n) 1) : ScalarDomain 2 :=
  sobolevOneToHilbertCLM ⟨z.val,by
    change Memℓp (fun n => (SpectralWeight.sobolev 1 (by norm_num) n : ℂ)*z.val n) 1
    simpa only [SpectralWeight.sobolev_apply] using hm⟩

@[simp] theorem fourierNLSHilbertData_apply (z : WeightedCoeff SpectralWeight.one.toWeight 1)
    (hm : Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*z.val n) 1) (n : ℤ) :
    (fourierNLSHilbertData z hm).val n = z.val n := by
  unfold fourierNLSHilbertData
  exact sobolevOneToHilbertCLM_apply _ n

end NLS.Fourier
