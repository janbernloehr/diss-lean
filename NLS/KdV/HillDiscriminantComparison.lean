import NLS.KdV.HillL2SpectralCriterion
import NLS.KdV.HillDiscriminantNecessity

/-! # Agreement of the classical and rough physical Hill characteristic equations -/

noncomputable section
open Set MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

theorem hillFirstOrder_continuous_compatibility (Q : C(AddCircle (2 : ℝ), ℂ)) :
    physicalBase (hillFirstOrderPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
      =ᵐ[volume.restrict (Ioc 0 1)] LinearVolterra.extend (constantUpperPotential (hillUnitPotentialCurve Q)) := by
  let C : C(AddCircle (2 : ℝ), ℂ) := ContinuousMap.const _ (-1)
  have hc : (lp.single 2 0 (-1) : Coeff 2) = Fourier.continuousFourierCLM C := by
    ext k
    rw [Fourier.continuousFourierCLM_apply]
    change (lp.single 2 0 (-1) : Coeff 2) k = fourierCoeff (fun _ : AddCircle (2 : ℝ) => (-1 : ℂ)) k
    rw [show (fun _ : AddCircle (2 : ℝ) => (-1 : ℂ)) =
      (fun x => (-1 : ℂ)*(fourier 0) x) by funext x; simp only [fourier_zero, mul_one],
      fourierCoeff.const_mul, fourierCoeff_fourier]
    by_cases hk : k = 0 <;> simp [lp.single_apply, hk]
  have hs : Fourier.l2Synthesis (lp.single 2 0 (-1)) = ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ C := by
    rw [hc]
    exact Fourier.l2Synthesis.apply_symm_apply _
  have hconst := Fourier.circle_ae_pullback
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle C)
  have hQ := Fourier.circle_ae_pullback
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle Q)
  have hn := Fourier.circle_ae_pullback (Lp.coeFn_neg (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ Q))
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hconst hQ hn ⊢
  filter_upwards [hconst, hQ, hn] with x hxC hxQ hxN
  intro hx
  have hx2 : x ∈ Ioc (0 : ℝ) 2 := ⟨hx.1,by linarith [hx.2]⟩
  have hxi : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le,hx.2⟩
  rw [LinearVolterra.extend, projIcc_of_mem _ hxi]
  change (Fourier.circlePullback (Fourier.l2Synthesis (lp.single 2 0 (-1))) x,
    Fourier.circlePullback (Fourier.l2Synthesis (-(SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))) x) =
      (-1,-Q (x : AddCircle (2 : ℝ)))
  rw [hs, map_neg, l2Synthesis_hillContinuousCoefficients]
  exact Prod.ext (hxC hx2) ((hxN hx2).trans (congrArg Neg.neg (hxQ hx2)))

/-- The rough physical monodromy trace agrees with the shared classical
Hill energy discriminant for every continuous potential. -/
theorem hillL2FrequencyDiscriminant_eq_classical (Q : C(AddCircle (2 : ℝ), ℂ)) (z : ℂ) :
    hillL2FrequencyDiscriminant (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z =
      classicalHillDiscriminant (hillUnitPotentialCurve Q) (z^2) := by
  rw [hillL2FrequencyDiscriminant, physicalRestrictionL2_of_continuous _ _
    (hillFirstOrder_continuous_compatibility Q), l2Discriminant_of_continuous,
    classicalHillDiscriminant_sq]

theorem hillContinuousCoefficients_mem_even (Q : C(AddCircle (2 : ℝ), ℂ))
    (hQ : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1) :
    SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0 := by
  apply (Coeff.mem_paritySubspace 0 _).mpr
  intro k hk
  have hk' : k = 2*(k/2)+1 := by omega
  simp only [SpectralWeight.toCoeff_apply, hillContinuousCoefficients_apply]
  rw [← Fourier.periodTwoCoefficient_circle, hk']
  exact Fourier.periodTwoCoefficient_periodic_odd _ hQ
    ((Q.continuous.comp (by fun_prop)).intervalIntegrable 0 1) (k/2)

/-- Full characteristic equivalence for the actual continuous period-one
potential, at every energy including zero. -/
theorem physicalHillEigenvector_iff_classicalDiscriminant
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hQ : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1) (lambda : ℂ) :
    (∃ f : HillSobolevDomain, f ≠ 0 ∧
      physicalHillOperator (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ Q) f =
        lambda • ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (hillRepresentative f)) ↔
      classicalHillDiscriminant (hillUnitPotentialCurve Q) lambda ^ 2 = 4 := by
  obtain ⟨z, rfl⟩ := IsAlgClosed.exists_pow_nat_eq lambda (by norm_num : 0 < 2)
  have h := hill_eigenvector_iff_l2FrequencyDiscriminant (hillContinuousCoefficients Q)
    (hillContinuousCoefficients_mem_even Q hQ) z
  rw [hillL2FrequencyDiscriminant_eq_classical] at h
  simp_rw [← physicalHillOperator_eigen_iff, l2Synthesis_hillContinuousCoefficients] at h
  exact h

end NLS.KdV
