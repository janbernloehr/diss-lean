import NLS.ZakharovShabat.ClassicalSolutionEnergyBound
import NLS.ZakharovShabat.ClassicalDiscriminantCommutation
import NLS.ZakharovShabat.ClassicalParityEigenvectors
import NLS.Fourier.UnitIntervalCoefficientDecay

/-! # Energy bounds for the actual discriminant gradient

The gradient is cubic in fundamental solutions. Its time derivative has
an integrable potential factor, so integrated physical energy controls its
variation even when the potential supremum is unbounded.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
namespace NLS.ZakharovShabat

private theorem column_energy_bounds (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0 : ℝ) 1) :
    ‖classicalSolution Φ z (1,0) t‖ ≤ Real.exp (‖z‖+1+classicalPotentialEnergy Φ) ∧
    ‖classicalSolution Φ z (0,1) t‖ ≤ Real.exp (‖z‖+1+classicalPotentialEnergy Φ) := by
  constructor
  · simpa using norm_classicalSolution_le_exp_energy Φ z (1,0) t
  · simpa using norm_classicalSolution_le_exp_energy Φ z (0,1) t

private theorem monodromy_energy_bound (Φ : Curve (ℂ × ℂ)) (z : ℂ) (i j : Fin 2) :
    ‖classicalMonodromy Φ z i j‖ ≤ Real.exp (‖z‖+1+classicalPotentialEnergy Φ) := by
  obtain ⟨ha,hb⟩ := column_energy_bounds Φ z ⟨1,by norm_num⟩
  fin_cases i <;> fin_cases j
  · exact (norm_fst_le _).trans ha
  · exact (norm_fst_le _).trans hb
  · exact (norm_snd_le _).trans ha
  · exact (norm_snd_le _).trans hb

private theorem cubic_bound (T : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ)
    (E : ℝ) (hE : 0 ≤ E) (hT : ∀ i j, ‖T i j‖ ≤ E) (ha : ‖a‖ ≤ E) (hb : ‖b‖ ≤ E) :
    ‖I*((T 0 0-T 1 1)*a*b-T 0 1*a^2+T 1 0*b^2)‖ ≤ 4*E^3 := by
  rw [norm_mul,norm_I,one_mul]
  calc
    _ ≤ (‖T 0 0‖+‖T 1 1‖)*‖a‖*‖b‖+‖T 0 1‖*‖a‖^2+‖T 1 0‖*‖b‖^2 := by
      apply (norm_add_le _ _).trans
      apply (add_le_add (norm_sub_le _ _) le_rfl).trans
      simp only [norm_mul,norm_pow]
      gcongr
      exact norm_sub_le _ _
    _ ≤ (E+E)*E*E+E*E^2+E*E^2 := by gcongr <;> apply hT
    _ = _ := by ring

/-- A uniform physical gradient bound uses only integrated energy. -/
theorem norm_classicalDiscriminantGradient_le_exp_energy
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    ‖classicalDiscriminantGradient Φ z t‖ ≤
      4*(Real.exp (‖z‖+1+classicalPotentialEnergy Φ))^3 := by
  obtain ⟨ha,hb⟩ := column_energy_bounds Φ z t
  apply norm_prod_le_iff.mpr
  constructor
  · exact cubic_bound _ _ _ _ (Real.exp_nonneg _) (monodromy_energy_bound Φ z)
      ((norm_snd_le _).trans ha) ((norm_snd_le _).trans hb)
  · exact cubic_bound _ _ _ _ (Real.exp_nonneg _) (monodromy_energy_bound Φ z)
      ((norm_fst_le _).trans ha) ((norm_fst_le _).trans hb)

/-- The transported diagonal term has the same cubic energy growth. -/
theorem norm_classicalDiscriminantDiagonal_le_exp_energy
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    ‖classicalDiscriminantDiagonal Φ z t‖ ≤
      8*(Real.exp (‖z‖+1+classicalPotentialEnergy Φ))^3 := by
  let E := Real.exp (‖z‖+1+classicalPotentialEnergy Φ)
  obtain ⟨ha,hb⟩ := column_energy_bounds Φ z t
  have ha₁ := (norm_fst_le _).trans ha
  have ha₂ := (norm_snd_le _).trans ha
  have hb₁ := (norm_fst_le _).trans hb
  have hb₂ := (norm_snd_le _).trans hb
  have hT := monodromy_energy_bound Φ z
  unfold classicalDiscriminantDiagonal
  dsimp only
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) le_rfl).trans
  simp only [norm_mul,norm_ofNat]
  calc
    _ ≤ (E+E)*(E*E+E*E)+2*E*E*E+2*E*E*E := by
      gcongr
      · exact (norm_sub_le _ _).trans (add_le_add (hT 0 0) (hT 1 1))
      · exact (norm_add_le _ _).trans (by simpa only [norm_mul] using
          (add_le_add (mul_le_mul ha₁ hb₂ (norm_nonneg _) (Real.exp_nonneg _))
            (mul_le_mul ha₂ hb₁ (norm_nonneg _) (Real.exp_nonneg _))))
      · exact hT 0 1
      · exact hT 1 0
    _ = _ := by dsimp [E]; ring

/-- The actual physical gradient is continuously differentiable in time. -/
theorem contDiff_classicalDiscriminantGradient (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    ContDiff ℝ 1 (classicalDiscriminantGradient Φ z) := by
  have ha := contDiff_classicalSolution Φ z (1,0)
  have hb := contDiff_classicalSolution Φ z (0,1)
  unfold classicalDiscriminantGradient
  fun_prop

/-- Each component's derivative has an integrable, energy-controlled bound. -/
theorem norm_deriv_classicalDiscriminantGradient_le_energy
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    ‖deriv (fun s => (classicalDiscriminantGradient Φ z s).1) t‖ ≤
      8*(Real.exp (‖z‖+1+classicalPotentialEnergy Φ))^3*(‖z‖+‖Φ t‖) ∧
    ‖deriv (fun s => (classicalDiscriminantGradient Φ z s).2) t‖ ≤
      8*(Real.exp (‖z‖+1+classicalPotentialEnergy Φ))^3*(‖z‖+‖Φ t‖) := by
  let E := Real.exp (‖z‖+1+classicalPotentialEnergy Φ)
  have hg := norm_classicalDiscriminantGradient_le_exp_energy Φ z t
  have hd := norm_classicalDiscriminantDiagonal_le_exp_energy Φ z t
  constructor
  · rw [(hasDerivAt_classicalDiscriminantGradient_fst Φ z t).deriv]
    apply (norm_add_le _ _).trans
    simp only [norm_mul,norm_ofNat,norm_I,mul_one]
    calc
      _ ≤ 2*‖z‖*(4*E^3)+‖Φ t‖*(8*E^3) := by
        gcongr
        · exact (norm_fst_le _).trans hg
        · exact norm_snd_le _
      _ = _ := by dsimp [E]; ring
  · rw [(hasDerivAt_classicalDiscriminantGradient_snd Φ z t).deriv]
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,norm_neg,norm_ofNat,norm_I,mul_one]
    calc
      _ ≤ 2*‖z‖*(4*E^3)+‖Φ t‖*(8*E^3) := by
        gcongr
        · exact (norm_snd_le _).trans hg
        · exact norm_fst_le _
      _ = _ := by dsimp [E]; ring

private theorem integral_derivative_bound (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hb : ∀ t : Icc (0 : ℝ) 1, ‖deriv f t‖ ≤
      8*(Real.exp (‖z‖+1+classicalPotentialEnergy Φ))^3*(‖z‖+‖Φ t‖)) :
    (∫ s in (0 : ℝ)..1, ‖deriv f s‖) ≤
      8*(Real.exp (‖z‖+1+classicalPotentialEnergy Φ))^3*(‖z‖+1+classicalPotentialEnergy Φ) := by
  let C := 8*(Real.exp (‖z‖+1+classicalPotentialEnergy Φ))^3
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((contDiff_one_iff_deriv.mp hf).2.norm.intervalIntegrable 0 1)
    ((continuous_const.mul (continuous_const.add (continuous_extend Φ).norm)).intervalIntegrable 0 1)
    (g := fun s => C*(‖z‖+‖extend Φ s‖)) (by
      intro s hs
      simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ hs] using hb ⟨s,hs⟩)
  rw [intervalIntegral.integral_const_mul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left
    (integral_classicalGrowthCoefficient_le_energy Φ z ⟨1,by norm_num⟩) (by positivity))

/-- Total variation of both physical gradient components is controlled by
energy, without any supremum bound on the potential. -/
theorem integral_norm_deriv_classicalDiscriminantGradient_le_energy
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    (∫ s in (0 : ℝ)..1, ‖deriv (fun t => (classicalDiscriminantGradient Φ z t).1) s‖) ≤
      8*(Real.exp (‖z‖+1+classicalPotentialEnergy Φ))^3*(‖z‖+1+classicalPotentialEnergy Φ) ∧
    (∫ s in (0 : ℝ)..1, ‖deriv (fun t => (classicalDiscriminantGradient Φ z t).2) s‖) ≤
      8*(Real.exp (‖z‖+1+classicalPotentialEnergy Φ))^3*(‖z‖+1+classicalPotentialEnergy Φ) := by
  exact ⟨integral_derivative_bound Φ z _ (contDiff_classicalDiscriminantGradient Φ z).fst
      (fun t => (norm_deriv_classicalDiscriminantGradient_le_energy Φ z t).1),
    integral_derivative_bound Φ z _ (contDiff_classicalDiscriminantGradient Φ z).snd
      (fun t => (norm_deriv_classicalDiscriminantGradient_le_energy Φ z t).2)⟩

/-- Every Fourier coefficient of either actual gradient component has
inverse-bracket decay with an energy-only constant, including frequency zero. -/
theorem norm_fourier_classicalDiscriminantGradient_le_energy
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℤ) :
    ‖intervalFourierCoefficient 1 (fun s => (classicalDiscriminantGradient Φ z s).1) n‖ ≤
      (8*(Real.exp (‖z‖+1+classicalPotentialEnergy Φ))^3*(‖z‖+2+classicalPotentialEnergy Φ))/(1+|(n : ℝ)|) ∧
    ‖intervalFourierCoefficient 1 (fun s => (classicalDiscriminantGradient Φ z s).2) n‖ ≤
      (8*(Real.exp (‖z‖+1+classicalPotentialEnergy Φ))^3*(‖z‖+2+classicalPotentialEnergy Φ))/(1+|(n : ℝ)|) := by
  let E := Real.exp (‖z‖+1+classicalPotentialEnergy Φ)
  have henergy := classicalPotentialEnergy_nonneg Φ
  have hconstant : 2*(4*E^3)+8*E^3*(‖z‖+1+classicalPotentialEnergy Φ) =
      8*E^3*(‖z‖+2+classicalPotentialEnergy Φ) := by ring
  obtain ⟨hd₁,hd₂⟩ := integral_norm_deriv_classicalDiscriminantGradient_le_energy Φ z
  constructor
  · have h := norm_unitIntervalFourierCoefficient_le_bracket_of_integral _
      (contDiff_classicalDiscriminantGradient Φ z).fst (4*E^3)
      (8*E^3*(‖z‖+1+classicalPotentialEnergy Φ)) (by positivity) (by positivity)
      (fun t ht => (norm_fst_le _).trans (norm_classicalDiscriminantGradient_le_exp_energy Φ z ⟨t,ht⟩)) hd₁ n
    rwa [hconstant] at h
  · have h := norm_unitIntervalFourierCoefficient_le_bracket_of_integral _
      (contDiff_classicalDiscriminantGradient Φ z).snd (4*E^3)
      (8*E^3*(‖z‖+1+classicalPotentialEnergy Φ)) (by positivity) (by positivity)
      (fun t ht => (norm_snd_le _).trans (norm_classicalDiscriminantGradient_le_exp_energy Φ z ⟨t,ht⟩)) hd₂ n
    rwa [hconstant] at h

end NLS.ZakharovShabat
