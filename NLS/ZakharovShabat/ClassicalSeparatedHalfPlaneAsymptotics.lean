import NLS.ZakharovShabat.ClassicalHalfPlaneAsymptotics
import NLS.ZakharovShabat.ClassicalSeparatedCharacteristics
import NLS.ZakharovShabat.ClassicalPhaseMonodromy
import NLS.ZakharovShabat.BoundaryCharacteristicExterior
import NLS.ZakharovShabat.ClassicalAuxiliarySpectralBridge

/-! # High-imaginary normalization of classical separated characteristics

The four weighted fundamental-matrix entries converge to their free values
in the upper half-plane. Their signed endpoint combination therefore has
the same leading exponential as the free sine, for either boundary condition.
-/

noncomputable section
open Set Complex Filter Topology
open NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

private theorem norm_classicalSeparated_upper_sub_free_le
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (hz : 0 < z.im) (hlarge : ‖Φ‖ ^ 2 ≤ z.im) :
    ‖exp (I*z) * classicalSeparatedCharacteristic b Φ z -
      (exp (2*I*z)-1)/(2*I)‖ ≤
      (2*‖Φ‖^2/(2*z.im) + 2*‖Φ‖/(2*z.im) +
        (‖Φ‖/(2*z.im) + 2*‖Φ‖^3/(2*z.im)^2) +
        2*‖Φ‖^2/(2*z.im)^2)/2 := by
  let t : Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
  let w00 := (classicalWeightedSolution Φ z (I*z) (1,0) 1).1
  let w10 := (classicalWeightedSolution Φ z (I*z) (1,0) 1).2
  let w01 := (classicalWeightedSolution Φ z (I*z) (0,1) 1).1
  let w11 := (classicalWeightedSolution Φ z (I*z) (0,1) 1).2
  have h₁ := classicalWeightedSolution_upper_bounds Φ z hz hlarge (1,0) t
  have h₂ := classicalWeightedSolution_upper_bounds Φ z hz hlarge (0,1) t
  have h00 : ‖w00-1‖ ≤ 2*‖Φ‖^2/(2*z.im) := by
    convert h₁.2.1 using 1
    simp only [norm_zero, norm_one, mul_zero, zero_div, add_zero, mul_one]
    ring
  have h10 : ‖w10‖ ≤ 2*‖Φ‖/(2*z.im) := by
    convert h₁.2.2 using 1
    all_goals simp [t, w10] <;> ring
  have h01 : ‖w01‖ ≤ ‖Φ‖/(2*z.im) + 2*‖Φ‖^3/(2*z.im)^2 := by
    convert h₂.2.1 using 1
    all_goals simp [t, w01] <;> ring
  have h11 : ‖w11-exp (2*I*z)‖ ≤ 2*‖Φ‖^2/(2*z.im)^2 := by
    convert h₂.2.2 using 1
    all_goals simp [t, w11] <;> ring
  have hs : ‖(extensionSign b : ℂ)‖ = 1 := by
    cases b <;> simp [extensionSign]
  have hw00 : w00 = exp (I*z) * classicalMonodromy Φ z 0 0 := by
    simp [w00, classicalWeightedSolution, classicalMonodromy, classicalFundamentalMatrix]
  have hw10 : w10 = exp (I*z) * classicalMonodromy Φ z 1 0 := by
    simp [w10, classicalWeightedSolution, classicalMonodromy, classicalFundamentalMatrix]
  have hw01 : w01 = exp (I*z) * classicalMonodromy Φ z 0 1 := by
    simp [w01, classicalWeightedSolution, classicalMonodromy, classicalFundamentalMatrix]
  have hw11 : w11 = exp (I*z) * classicalMonodromy Φ z 1 1 := by
    simp [w11, classicalWeightedSolution, classicalMonodromy, classicalFundamentalMatrix]
  have he : exp (I*z) * classicalSeparatedCharacteristic b Φ z -
      (exp (2*I*z)-1)/(2*I) =
      ((w11-exp (2*I*z)) - (w00-1) + extensionSign b * (w10-w01))/(2*I) := by
    rw [hw00, hw10, hw01, hw11]
    unfold classicalSeparatedCharacteristic
    ring
  rw [he, norm_div]
  have hnum : ‖(w11-exp (2*I*z)) - (w00-1) +
      extensionSign b * (w10-w01)‖ ≤
      ‖w11-exp (2*I*z)‖ + ‖w00-1‖ + ‖w10‖ + ‖w01‖ := by
    calc
      _ ≤ ‖(w11-exp (2*I*z)) - (w00-1)‖ +
          ‖extensionSign b * (w10-w01)‖ := norm_add_le _ _
      _ ≤ (‖w11-exp (2*I*z)‖ + ‖w00-1‖) +
          (‖w10‖ + ‖w01‖) := by
        rw [norm_mul, hs, one_mul]
        exact add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
      _ = _ := by ring
  have hbound : ‖w11-exp (2*I*z)‖ + ‖w00-1‖ + ‖w10‖ + ‖w01‖ ≤
      2*‖Φ‖^2/(2*z.im)^2 + 2*‖Φ‖^2/(2*z.im) +
        2*‖Φ‖/(2*z.im) + (‖Φ‖/(2*z.im) + 2*‖Φ‖^3/(2*z.im)^2) := by
    linarith
  have hden : ‖(2*I : ℂ)‖ = 2 := by simp
  rw [hden]
  apply (div_le_div_of_nonneg_right (hnum.trans hbound) (by norm_num)).trans
  ring_nf
  exact le_refl _

private theorem tendsto_upper_error {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto y l atTop) (M : ℝ) :
    Tendsto (fun i => (2*M^2/(2*y i) + 2*M/(2*y i) +
      (M/(2*y i) + 2*M^3/(2*y i)^2) + 2*M^2/(2*y i)^2)/2) l (𝓝 0) := by
  have hd : Tendsto (fun i => 2*y i) l atTop :=
    hy.const_mul_atTop (by norm_num)
  have hd₂ : Tendsto (fun i => (2*y i)^2) l atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hd
  have h := (((hd.const_div_atTop (2*M^2)).add (hd.const_div_atTop (2*M))).add
    ((hd.const_div_atTop M).add (hd₂.const_div_atTop (2*M^3)))).add
      (hd₂.const_div_atTop (2*M^2))
  simpa only [zero_add, zero_div] using h.div_const 2

/-- The upper-normalized classical separated characteristic differs from its free value by a vanishing error. -/
theorem tendsto_classicalSeparated_upper_sub_free {α : Type*} {l : Filter α}
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : α → ℂ)
    (hz : Tendsto (fun i => (z i).im) l atTop) :
    Tendsto (fun i => exp (I*z i) * classicalSeparatedCharacteristic b Φ (z i) -
      (exp (2*I*z i)-1)/(2*I)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (tendsto_upper_error hz ‖Φ‖)
  filter_upwards [hz.eventually_ge_atTop 1,
    hz.eventually_ge_atTop (‖Φ‖^2)] with i hi hlarge
  exact norm_classicalSeparated_upper_sub_free_le b Φ (z i) (by linarith) hlarge

/-- The upper-normalized classical characteristic has the same nonzero leading constant as free sine. -/
theorem tendsto_classicalSeparated_upper_normalized {α : Type*} {l : Filter α}
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : α → ℂ)
    (hz : Tendsto (fun i => (z i).im) l atTop) :
    Tendsto (fun i => exp (I*z i) * classicalSeparatedCharacteristic b Φ (z i))
      l (𝓝 (-1/(2*I))) := by
  have he : Tendsto (fun i => exp (2*I*z i)) l (𝓝 0) := by
    apply Complex.tendsto_exp_nhds_zero_iff.mpr
    simpa [Complex.mul_re, Function.comp_def] using
      tendsto_neg_atTop_atBot.comp (hz.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hf : Tendsto (fun i => (exp (2*I*z i)-1)/(2*I)) l (𝓝 (-1/(2*I))) := by
    simpa only [zero_sub] using (he.sub_const 1).div_const (2*I)
  simpa only [sub_add_cancel, zero_add] using
    (tendsto_classicalSeparated_upper_sub_free b Φ z hz).add hf

/-- Both classical separated characteristics have ratio one to free sine at the upper imaginary end. -/
theorem tendsto_classicalSeparated_div_sin_upper {α : Type*} {l : Filter α}
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : α → ℂ)
    (hz : Tendsto (fun i => (z i).im) l atTop) :
    Tendsto (fun i => classicalSeparatedCharacteristic b Φ (z i) / sin (z i))
      l (𝓝 1) := by
  have hsin : Tendsto (fun i => exp (I*z i) * sin (z i))
      l (𝓝 (-1/(2*I))) := by
    simpa only [classicalSeparatedCharacteristic_free] using
      tendsto_classicalSeparated_upper_normalized b (0 : Curve (ℂ × ℂ)) z hz
  have hn : (-1/(2*I) : ℂ) ≠ 0 := by norm_num
  have h := (tendsto_classicalSeparated_upper_normalized b Φ z hz).div hsin hn
  change Tendsto (fun i =>
    (exp (I*z i) * classicalSeparatedCharacteristic b Φ (z i)) /
      (exp (I*z i) * sin (z i))) l
        (𝓝 ((-1/(2*I) : ℂ)/(-1/(2*I)))) at h
  simpa only [mul_div_mul_left _ _ (exp_ne_zero _), div_self hn] using! h

/-- The actual classical auxiliary characteristics have the same upper free-sine normalization. -/
theorem tendsto_classicalAuxiliary_div_sin_upper {α : Type*} {l : Filter α}
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : α → ℂ)
    (hz : Tendsto (fun i => (z i).im) l atTop) :
    Tendsto (fun i => classicalAuxiliaryCharacteristic b Φ (z i) / sin (z i))
      l (𝓝 1) := by
  simpa only [classicalAuxiliaryCharacteristic_eq_separated_phase] using
    tendsto_classicalSeparated_div_sin_upper b (classicalSourcePhase Φ) z hz

/-- On upper separated paths, the classical and intrinsic ordinary boundary characteristics have quotient limit one. -/
theorem tendsto_classicalSeparated_div_characteristic_upper_of_separated
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (z : α → ℂ) (hz : Tendsto (fun i => (z i).im) l atTop)
    (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i - (Real.pi : ℂ) * n‖) :
    Tendsto (fun i => classicalSeparatedCharacteristic b Φ (z i) /
      b.characteristic hp φ hφ (z i)) l (𝓝 1) := by
  have hχ := tendsto_classicalSeparated_div_sin_upper b Φ z hz
  have hg := b.tendsto_characteristic_div_sin_of_separated hp hp1 φ hφ
    z hescape hr hrπ hsep
  have h := hχ.div hg (by norm_num : (1 : ℂ) ≠ 0)
  have he (i : α) : classicalSeparatedCharacteristic b Φ (z i) /
      b.characteristic hp φ hφ (z i) =
      (classicalSeparatedCharacteristic b Φ (z i) / sin (z i)) /
        (b.characteristic hp φ hφ (z i) / sin (z i)) := by
    have hs : sin (z i) ≠ 0 := sin_ne_zero_of_notMem_freeLattice
      (notMem_freeLattice_of_separated hr (hsep i))
    rw [div_div_div_cancel_right₀ hs]
  change Tendsto (fun i => (classicalSeparatedCharacteristic b Φ (z i) / sin (z i)) /
    (b.characteristic hp φ hφ (z i) / sin (z i))) l (𝓝 ((1 : ℂ)/1)) at h
  simpa only [← he, div_self (by norm_num : (1 : ℂ) ≠ 0)] using h

/-- The actual classical and normalized starred characteristics have quotient limit one on upper separated paths. -/
theorem tendsto_classicalAuxiliary_div_source_upper_of_separated
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (φ : CoeffPair p)
    (z : α → ℂ) (hz : Tendsto (fun i => (z i).im) l atTop)
    (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i - (Real.pi : ℂ) * n‖) :
    Tendsto (fun i => classicalAuxiliaryCharacteristic b Φ (z i) /
      auxiliaryPeriodOneCharacteristic hp hp1 b φ (z i)) l (𝓝 1) := by
  have hχ := tendsto_classicalAuxiliary_div_sin_upper b Φ z hz
  have hg := tendsto_auxiliaryPeriodOneCharacteristic_div_sin_of_separated
    hp hp1 b φ z hescape hr hrπ hsep
  have h := hχ.div hg (by norm_num : (1 : ℂ) ≠ 0)
  have he (i : α) : classicalAuxiliaryCharacteristic b Φ (z i) /
      auxiliaryPeriodOneCharacteristic hp hp1 b φ (z i) =
      (classicalAuxiliaryCharacteristic b Φ (z i) / sin (z i)) /
        (auxiliaryPeriodOneCharacteristic hp hp1 b φ (z i) / sin (z i)) := by
    have hs : sin (z i) ≠ 0 := sin_ne_zero_of_notMem_freeLattice
      (notMem_freeLattice_of_separated hr (hsep i))
    rw [div_div_div_cancel_right₀ hs]
  change Tendsto (fun i => (classicalAuxiliaryCharacteristic b Φ (z i) / sin (z i)) /
    (auxiliaryPeriodOneCharacteristic hp hp1 b φ (z i) / sin (z i)))
      l (𝓝 ((1 : ℂ)/1)) at h
  simpa only [← he, div_self (by norm_num : (1 : ℂ) ≠ 0)] using h

/-- At finite source data, the two actual auxiliary characteristic realizations have quotient limit one. -/
theorem tendsto_classicalAuxiliary_finite_div_source_upper_of_separated
    {α : Type*} {l : Filter α} (b : BoundaryCondition)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : α → ℂ)
    (hz : Tendsto (fun i => (z i).im) l atTop)
    (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i - (Real.pi : ℂ) * n‖) :
    Tendsto (fun i => classicalAuxiliaryCharacteristic b (finiteSourceCurve a) (z i) /
      auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) b
        (CoeffPair.ofFinsupp (p := 2) a) (z i)) l (𝓝 1) :=
  tendsto_classicalAuxiliary_div_source_upper_of_separated
    (by simp) (by norm_num) b (finiteSourceCurve a)
      (CoeffPair.ofFinsupp (p := 2) a) z hz hescape hr hrπ hsep

end NLS.ZakharovShabat
