import NLS.ZakharovShabat.BoundaryCharacteristicExterior
import NLS.ZakharovShabat.ClassicalHorizontalStripBounds
import NLS.ZakharovShabat.ClassicalSeparatedCharacteristics

/-! # Exterior growth bounds for classical separated characteristics

The monodromy's four entries grow at most exponentially in the imaginary
spectral height. Combined with the normalized source product's exterior
lower bound, this controls the classical-to-intrinsic ratio away from the
free-root discs. Extending that ratio through its zeros remains separate.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- A classical separated characteristic has sine-scale growth, uniformly in the real spectral part. -/
theorem norm_classicalSeparatedCharacteristic_le_exp_im (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    ‖classicalSeparatedCharacteristic b Φ z‖ ≤
      2 * Real.exp (|z.im| + ‖Φ‖) := by
  let E := Real.exp (|z.im| + ‖Φ‖)
  let t : Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
  have h₁ := norm_classicalSolution_le_exp_im Φ z (1,0) t
  have h₂ := norm_classicalSolution_le_exp_im Φ z (0,1) t
  have h₁' : ‖classicalSolution Φ z (1,0) 1‖ ≤ E := by
    simpa [t, E, Prod.norm_def] using h₁
  have h₂' : ‖classicalSolution Φ z (0,1) 1‖ ≤ E := by
    simpa [t, E, Prod.norm_def] using h₂
  have h00 : ‖classicalMonodromy Φ z 0 0‖ ≤ E := by
    exact (norm_fst_le _).trans h₁'
  have h10 : ‖classicalMonodromy Φ z 1 0‖ ≤ E := by
    exact (norm_snd_le _).trans h₁'
  have h01 : ‖classicalMonodromy Φ z 0 1‖ ≤ E := by
    exact (norm_fst_le _).trans h₂'
  have h11 : ‖classicalMonodromy Φ z 1 1‖ ≤ E := by
    exact (norm_snd_le _).trans h₂'
  have hs : ‖(extensionSign b : ℂ)‖ = 1 := by
    cases b <;> simp [extensionSign]
  have hnum : ‖classicalMonodromy Φ z 1 1 - classicalMonodromy Φ z 0 0 +
      extensionSign b * (classicalMonodromy Φ z 1 0 - classicalMonodromy Φ z 0 1)‖ ≤ 4 * E := by
    calc
      _ ≤ ‖classicalMonodromy Φ z 1 1 - classicalMonodromy Φ z 0 0‖ +
          ‖extensionSign b * (classicalMonodromy Φ z 1 0 - classicalMonodromy Φ z 0 1)‖ :=
        norm_add_le _ _
      _ ≤ (‖classicalMonodromy Φ z 1 1‖ + ‖classicalMonodromy Φ z 0 0‖) +
          (‖classicalMonodromy Φ z 1 0‖ + ‖classicalMonodromy Φ z 0 1‖) := by
        rw [norm_mul, hs, one_mul]
        exact add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
      _ ≤ 4 * E := by linarith
  calc
    ‖classicalSeparatedCharacteristic b Φ z‖ =
        ‖classicalMonodromy Φ z 1 1 - classicalMonodromy Φ z 0 0 +
          extensionSign b * (classicalMonodromy Φ z 1 0 - classicalMonodromy Φ z 0 1)‖ / 2 := by
      simp [classicalSeparatedCharacteristic]
    _ ≤ 4 * E / 2 := by exact div_le_div_of_nonneg_right hnum (by norm_num)
    _ = 2 * Real.exp (|z.im| + ‖Φ‖) := by dsimp [E]; ring

/-- The classical characteristic divided by free sine is uniformly bounded away from fixed free-root discs. -/
theorem exists_bound_classicalSeparatedCharacteristic_div_sin_of_separated
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    {r : ℝ} (hr : 0 < r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ,
      (∀ n : ℤ, r ≤ ‖z - (Real.pi : ℂ) * n‖) →
        ‖classicalSeparatedCharacteristic b Φ z / sin z‖ ≤ B := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_exp_im_div_sin_of_separated hr
  refine ⟨2 * Real.exp ‖Φ‖ * C, by positivity, ?_⟩
  intro z hsep
  have hχ := norm_classicalSeparatedCharacteristic_le_exp_im b Φ z
  have hs := hbound z hsep
  rw [norm_div] at hs ⊢
  have hsin : 0 ≤ ‖sin z‖ := norm_nonneg _
  have hscale : ‖(Real.exp |z.im| : ℂ)‖ = Real.exp |z.im| := by simp
  rw [hscale] at hs
  rw [Real.exp_add] at hχ
  have hn : ‖classicalSeparatedCharacteristic b Φ z‖ ≤
      2 * Real.exp ‖Φ‖ * Real.exp |z.im| := by
    convert hχ using 1
    ring
  calc
    ‖classicalSeparatedCharacteristic b Φ z‖ / ‖sin z‖ ≤
        (2 * Real.exp ‖Φ‖ * Real.exp |z.im|) / ‖sin z‖ := by
      exact div_le_div_of_nonneg_right hn hsin
    _ = 2 * Real.exp ‖Φ‖ * (Real.exp |z.im| / ‖sin z‖) := by ring
    _ ≤ 2 * Real.exp ‖Φ‖ * C := by
      exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- The classical-to-intrinsic ratio is bounded on the large separated exterior. -/
theorem exists_bound_classicalSeparated_div_characteristic_exterior
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) :
    ∃ R B : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ n : ℤ, r ≤ ‖z - (Real.pi : ℂ) * n‖) →
        ‖classicalSeparatedCharacteristic b Φ z /
          b.characteristic hp φ hφ z‖ ≤ B := by
  obtain ⟨B, _, hχ⟩ := exists_bound_classicalSeparatedCharacteristic_div_sin_of_separated b Φ hr
  obtain ⟨R, hR⟩ := b.exists_threshold_half_le_norm_characteristic_div_sin
    hp hp1 φ hφ hr hrπ
  refine ⟨R, 2 * B, ?_⟩
  intro z hz hsep
  have hl := hR z hz hsep
  have hg : b.characteristic hp φ hφ z ≠ 0 := by
    intro hg
    simp only [hg, zero_div, norm_zero] at hl
    norm_num at hl
  have hs : sin z ≠ 0 := sin_ne_zero_of_notMem_freeLattice
    (notMem_freeLattice_of_separated hr hsep)
  rw [← div_div_div_cancel_right₀ hs, norm_div]
  have hpos : (0 : ℝ) < ‖b.characteristic hp φ hφ z / sin z‖ := by linarith
  apply (div_le_iff₀ hpos).mpr
  calc
    ‖classicalSeparatedCharacteristic b Φ z / sin z‖ ≤ B := hχ z hsep
    _ ≤ 2 * B * ‖b.characteristic hp φ hφ z / sin z‖ := by
      have hB : 0 ≤ B := le_trans (norm_nonneg _) (hχ z hsep)
      nlinarith

end NLS.ZakharovShabat
