import NLS.ZakharovShabat.PhysicalParity
import NLS.FunctionalAnalysis.LinearVolterraRegularity
import NLS.ZakharovShabat.ClassicalBoundaryDeterminants

/-!
# Original parity eigenvectors give classical monodromy roots

For a Hilbert coefficient potential with a continuous representative on the
unit interval, its original domain eigenvectors agree there with the constructed
classical solutions. Fourier parity supplies their endpoint multipliers, and
nonzero parity eigenvectors have nonzero initial vectors.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The physical spectral equation determines the derivative of a differentiable vector. -/
theorem hasDerivAt_of_physicalOperator_eq {u : ℝ → ℂ × ℂ} {φ : ℝ → ℂ × ℂ}
    {z : ℂ} {t : ℝ} (h₁ : DifferentiableAt ℝ (fun s => (u s).1) t)
    (h₂ : DifferentiableAt ℝ (fun s => (u s).2) t)
    (he : physicalOperator φ u t = z • u t) :
    HasDerivAt u (classicalODECoefficient (φ t) z (u t)) t := by
  have he₁ := congrArg Prod.fst he
  have he₂ := congrArg Prod.snd he
  change I * deriv (fun s => (u s).1) t + (φ t).1 * (u t).2 = z * (u t).1 at he₁
  change -I * deriv (fun s => (u s).2) t + (φ t).2 * (u t).1 = z * (u t).2 at he₂
  have hd := h₁.hasDerivAt.prodMk h₂.hasDerivAt
  convert! hd.congr_deriv (show (deriv (fun s => (u s).1) t,deriv (fun s => (u s).2) t) =
      classicalODECoefficient (φ t) z (u t) by
    apply Prod.ext
    · dsimp
      linear_combination (norm := (ring_nf; simp [I_sq])) -I * he₁
    · dsimp
      linear_combination (norm := (ring_nf; simp [I_sq])) I * he₂) using 1

/-- Original Hilbert eigenvectors solve the continuous-coefficient ODE almost everywhere. -/
theorem ae_hasDerivAt_physicalDomain_eigenvector (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (a : Domain 2) (z : ℂ) (he : operator (by simp) φ a = z • domainInclusion a) :
    ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (physicalDomain a) (extend (classicalODECurve Φ z) s (physicalDomain a s)) s := by
  have hO := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num))
    ((operator_eq_smul_iff_physical φ a z).mp he)
  rw [ae_restrict_iff' measurableSet_Ioc] at hO
  simp only [Filter.EventuallyEq,ae_restrict_iff' measurableSet_Ioc] at hΦ
  filter_upwards [hO,hΦ,
    NLS.FunctionalAnalysis.ae_differentiableAt_complex (absolutelyContinuous_sobolevSynthesis a.1),
    NLS.FunctionalAnalysis.ae_differentiableAt_complex (absolutelyContinuous_sobolevSynthesis a.2),
    (show ∀ᵐ s : ℝ, s ≠ (0 : ℝ) from by simp [ae_iff,measure_singleton])]
      with s hsO hsΦ hs₁ hs₂ hs0
  intro hs
  have hs' : s ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),hs.2⟩
  have hs2 : s ∈ uIcc (0 : ℝ) 2 := by
    rw [uIcc_of_le (by norm_num)]
    exact ⟨hs.1,hs.2.trans (by norm_num)⟩
  have hD := hasDerivAt_of_physicalOperator_eq (hs₁ hs2) (hs₂ hs2) (hsO hs')
  rw [hsΦ hs'] at hD
  exact hD

/-- An original Hilbert eigenvector is the classical solution with its own initial value. -/
theorem physicalDomain_eq_classicalSolution (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (a : Domain 2) (z : ℂ) (he : operator (by simp) φ a = z • domainInclusion a) :
    EqOn (physicalDomain a) (classicalSolution Φ z (physicalDomain a 0)) (Icc 0 1) := by
  apply solution_unique_of_ac
  · exact (absolutelyContinuous_physicalDomain a).mono (by
      simp only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num),
        uIcc_of_le (show (0 : ℝ) ≤ 2 by norm_num)]
      exact Icc_subset_Icc le_rfl (by norm_num))
  · exact ae_hasDerivAt_physicalDomain_eigenvector φ Φ hΦ a z he

/-- Zero initial data give the zero classical solution throughout the unit interval. -/
theorem classicalSolution_zero_initial (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution Φ z 0 t = 0 := by
  rw [classicalSolution_eq_columns]
  simp

/-- A nonzero original parity eigenvector cannot have zero initial data. -/
theorem physicalDomain_initial_ne_zero_of_parity_eigenvector
    (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (a : Domain 2) (r : ℤ) (ha : a ∈ domainParitySubspace r) (hne : a ≠ 0)
    (z : ℂ) (he : operator (by simp) φ a = z • domainInclusion a) : physicalDomain a 0 ≠ 0 := by
  intro hz
  apply hne
  apply (physicalDomain_eq_zero_on_unit_iff a r ha).mp
  have h := physicalDomain_eq_classicalSolution φ Φ hΦ a z he
  intro t ht
  rw [h ht,hz]
  exact classicalSolution_zero_initial Φ z ⟨t,ht⟩

/-- Fourier parity gives an actual nonzero classical solution with the same endpoint multiplier. -/
theorem classicalSolution_endpoint_of_parity_eigenvector
    (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (a : Domain 2) (r : ℤ) (ha : a ∈ domainParitySubspace r) (hne : a ≠ 0)
    (z : ℂ) (he : operator (by simp) φ a = z • domainInclusion a) :
    ∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalSolution Φ z v 1 = wave r 1 • v := by
  refine ⟨physicalDomain a 0,
    physicalDomain_initial_ne_zero_of_parity_eigenvector φ Φ hΦ a r ha hne z he,?_⟩
  rw [← physicalDomain_eq_classicalSolution φ Φ hΦ a z he (show (1 : ℝ) ∈ Icc 0 1 by simp)]
  simpa only [zero_add] using physicalDomain_add_one_of_parity a r ha 0

/-- An original parity eigenvector forces the corresponding monodromy characteristic determinant to vanish. -/
theorem det_classicalMonodromy_eq_zero_of_parity_eigenvector
    (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (a : Domain 2) (r : ℤ) (ha : a ∈ domainParitySubspace r) (hne : a ≠ 0)
    (z : ℂ) (he : operator (by simp) φ a = z • domainInclusion a) :
    (classicalMonodromy Φ z - wave r 1 • 1).det = 0 :=
  (det_classicalMonodromy_sub_scalar_eq_zero_iff Φ z (wave r 1)).mpr
    (classicalSolution_endpoint_of_parity_eigenvector φ Φ hΦ a r ha hne z he)

end NLS.ZakharovShabat
