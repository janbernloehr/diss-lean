import NLS.ZakharovShabat.ResonantCubicPerturbationTail

/-! # Exact cubic background and control of differences of strip suprema -/
noncomputable section
open NLS NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The two-mode background scales by its raw Fourier amplitude. -/
theorem twoModeResonantPotential_smul (w : SpectralWeight) (n : ℤ) (s : ℂ) :
    s • twoModeResonantPotential (p := p) w n 1 = twoModeResonantPotential w n s := by
  unfold twoModeResonantPotential
  rw [← map_smul]
  congr 1
  ext <;> simp [smul_add,← map_smul,smul_eq_mul]

/-- The actual scaled-background cubic term is supported at the target tail index. -/
theorem resonantCubicTermFunction_twoMode (hp : p ≠ ⊤) (w : SpectralWeight)
    (n m : ℤ) (hn : 0 < n) (hm : n ≤ |m|) (s z : ℂ) (hz : z ∈ resonantStrip m)
    (positive : Bool) :
    resonantCubicTermFunction hp w (s • twoModeResonantPotential w n 1) m positive z =
      if m=n then s^3/z^2 else 0 := by
  rw [twoModeResonantPotential_smul]
  cases positive
  · simpa only [resonantCubicTermFunction,Bool.false_eq_true,if_false,
      weightedResonantParityTermFunction,weightedPotentialExtension_eq hp w _ m z hz,
      pow_zero,pow_two,one_apply_eq_self,mul_apply_eq_comp,resonantCoordinates_zero] using
      twoModeResonantPotential_cubic_negative hp w n m hn hm s z hz
  · simpa only [resonantCubicTermFunction,if_true,
      weightedResonantParityTermFunction,weightedPotentialExtension_eq hp w _ m z hz,
      pow_zero,pow_two,one_apply_eq_self,mul_apply_eq_comp,resonantCoordinates_one] using
      twoModeResonantPotential_cubic_positive hp w n m hn hm s z hz

/-- Every weighted pointwise cubic perturbation is controlled by its actual full-strip supremum. -/
theorem resonantCubicPerturbationSup_pointwise (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B : WeightedCoeffPair w.toWeight p) (m : ℤ) (s z : ℂ)
    (hs : ‖s‖ ≤ 1) (hz : z ∈ resonantStrip m) (i j : Fin 2) :
    w (2*m)*‖weightedResonantParityTermFunction hp w (s • A+s^3 • B) m 2 0 i j z -
      weightedResonantParityTermFunction hp w (s • A) m 2 0 i j z‖ ≤
      resonantCubicPerturbationSup hp w A B m s i j := by
  exact (weightedStripSup_bounds w m
    (fun z => weightedResonantParityTermFunction hp w (s • A+s^3 • B) m 2 0 i j z -
      weightedResonantParityTermFunction hp w (s • A) m 2 0 i j z) (w (2*m)*‖s‖^5*resonantCubicPerturbationBound hp w A B m j)
    (by
      intro z hz
      rw [resonantCubic_homogeneous]
      exact (mul_le_mul_of_nonneg_left (resonantCubicPerturbation_norm_le hp w A B m z s hz hs i j)
        (w.positive _).le).trans_eq (by ring))).2.2 z hz

/-- Uniform norm differences control differences of the actual unit-weight strip suprema. -/
theorem unitWeightedStripSup_difference (m : ℤ) (f g : ℂ → ℂ) (E G : ℝ)
    (hg : ∀ z ∈ resonantStrip m, ‖g z‖ ≤ G)
    (he : ∀ z ∈ resonantStrip m, ‖f z-g z‖ ≤ E) :
    0 ≤ weightedStripSup SpectralWeight.one m f ∧
    |weightedStripSup SpectralWeight.one m f-weightedStripSup SpectralWeight.one m g| ≤ E := by
  have hfg (z : ℂ) : ‖f z‖ ≤ ‖g z‖+‖f z-g z‖ := by
    calc
      _ = ‖g z+(f z-g z)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hgf (z : ℂ) : ‖g z‖ ≤ ‖f z‖+‖f z-g z‖ := by
    simpa only [norm_sub_rev] using norm_le_insert' (g z) (f z)
  have hg' := weightedStripSup_bounds SpectralWeight.one m g G (by simpa using hg)
  have hf' := weightedStripSup_bounds SpectralWeight.one m f (G+E) (by
    intro z hz
    simpa using (hfg z).trans (add_le_add (hg z hz) (he z hz)))
  refine ⟨hf'.1,abs_le.mpr ⟨?_,?_⟩⟩
  · have h := (weightedStripSup_bounds SpectralWeight.one m g
        (weightedStripSup SpectralWeight.one m f+E) (by
          intro z hz
          have hval := hf'.2.2 z hz
          simp only [SpectralWeight.one_apply,one_mul] at hval ⊢
          exact (hgf z).trans (add_le_add hval (he z hz)))).2.1
    linarith
  · have h := (weightedStripSup_bounds SpectralWeight.one m f
        (weightedStripSup SpectralWeight.one m g+E) (by
          intro z hz
          have hval := hg'.2.2 z hz
          simp only [SpectralWeight.one_apply,one_mul] at hval ⊢
          exact (hfg z).trans (add_le_add hval (he z hz)))).2.1
    linarith

end NLS.ZakharovShabat
