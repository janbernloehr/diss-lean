import NLS.Articles.KdVPseudomeasures.SpectralLowerBound

/-!
# A uniform physical resolvent boundary around the finite central spectrum

The same rectangle works for every original complex endpoint potential in a
specified norm ball. Its left and horizontal sides use the proved form bound;
its right side uses the actual wide localization. The central spectral count
inside is not assumed to equal the free count.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- A uniform height strictly beyond the actual complex central spectrum. -/
def sourceCentralWindowHeight (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (N : ℕ) : ℝ :=
  |freeHillValue N-12*(N:ℝ)|+2*sourceSpectralBound r hr R+1

/-- The three side conditions describe the full boundary of the chosen central rectangle. -/
def sourceCentralWindowBoundary (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (N : ℕ) : Set ℂ :=
  {z | (z.re = -sourceSpectralBound r hr R-1 ∧ |z.im| ≤ sourceCentralWindowHeight r hr R N) ∨
    (z.re = freeHillValue N-12*(N:ℝ) ∧ |z.im| ≤ sourceCentralWindowHeight r hr R N) ∨
    (-sourceSpectralBound r hr R-1 ≤ z.re ∧ z.re ≤ freeHillValue N-12*(N:ℝ) ∧
      |z.im| = sourceCentralWindowHeight r hr R N)}

/-- The rectangle has positive height. -/
theorem sourceCentralWindowHeight_pos (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (N : ℕ) :
    0 < sourceCentralWindowHeight r hr R N := by
  have h := sourceSpectralBound_nonneg r hr R
  unfold sourceCentralWindowHeight
  positivity

/-- The rectangle has a nonempty real interior for every admissible high cutoff. -/
theorem sourceCentralWindow_left_lt_right (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (hN : 2 ≤ N) : -sourceSpectralBound r hr R-1 < freeHillValue N-12*(N:ℝ) := by
  have hc := sourceSpectralBound_nonneg r hr R
  have he := (freeHillCentralEdge_between N hN).1
  have hfree : 0 ≤ freeHillValue ((N-1:ℕ):ℤ) := by unfold freeHillValue; positivity
  linarith

/-- Every boundary point lies in the full original H1-to-H-minus-one resolvent,
uniformly on the original COMPLEX potential norm ball. -/
theorem sourceCentralWindowBoundary_bijective (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (hN : 2 ≤ N)
    (hcut : 13*endpointHillConstant r*(N:ℝ)^(r-1/2)*R ≤ 1/2)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R)
    (z : ℂ) (hz : z ∈ sourceCentralWindowBoundary r hr R N) :
    Function.Bijective (singularHillOperator (sourceComplexHminusOne r hr q)-z • singularHillDomainInclusion) := by
  rcases hz with hz | hz | hz
  · apply sourceHillPencil_bijective_of_re_lt_on_ball r hr R q hq z
    linarith [hz.1]
  · by_contra hnot
    have hs : 13*endpointHillConstant r*(N:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 :=
      (mul_le_mul_of_nonneg_left hq (mul_nonneg
        (mul_nonneg (by norm_num) (endpointHillConstant_pos r hr.2).le)
        (Real.rpow_nonneg (by positivity) _))).trans hcut
    have hwide : z ∈ wideHillStrip N := by
      change |z.re-freeHillValue N| ≤ 12*(N:ℝ)
      rw [hz.1]
      simp only [sub_sub_cancel_left,abs_neg,abs_of_nonneg (by positivity : 0 ≤ 12*(N:ℝ))]
      exact le_rfl
    have hloc := (sourceHillSpectrum_wide_localization r hr N hN q hs z hwide hnot).2
    have hRe := Complex.abs_re_le_norm (z-(freeHillValue N:ℂ))
    simp only [Complex.sub_re,Complex.ofReal_re] at hRe
    rw [hz.1] at hRe
    have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
    have hsq : Real.sqrt (N:ℝ) ≤ N := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
    have ha : |freeHillValue N-12*(N:ℝ)-freeHillValue N| = 12*(N:ℝ) := by
      rw [sub_sub_cancel_left,abs_neg,abs_of_nonneg (by positivity)]
    rw [ha] at hRe
    linarith
  · by_contra hnot
    have him := sourceHillSpectrum_abs_im_le_on_ball r hr R q hq z hnot
    rw [hz.2.2] at him
    unfold sourceCentralWindowHeight at him
    linarith [hz.2.1,le_abs_self (freeHillValue N-12*(N:ℝ))]

/-- Every actual central spectral point is strictly inside the same rectangle. -/
theorem sourceCentralSpectrum_inside_window (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) (N : ℕ)
    (z : ℂ) (hz : z ∈ sourceCentralSpectrum r hr q N) :
    -sourceSpectralBound r hr R-1 < z.re ∧ z.re < freeHillValue N-12*(N:ℝ) ∧
      |z.im| < sourceCentralWindowHeight r hr R N := by
  obtain ⟨hspec,hlt⟩ := (mem_sourceCentralSpectrum r hr q N z).mp hz
  have hre := sourceHillSpectrum_re_lower_bound_on_ball r hr R q hq z hspec
  have him := sourceHillSpectrum_abs_im_le_on_ball r hr R q hq z hspec
  refine ⟨by linarith,hlt,?_⟩
  unfold sourceCentralWindowHeight
  linarith [le_abs_self (freeHillValue N-12*(N:ℝ))]

/-- A cutoff chosen before the original complex potential gives one actual
resolvent boundary enclosing its finite central spectrum on the entire norm ball. -/
theorem source_uniform_central_resolvent_window (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      (∀ z ∈ sourceCentralWindowBoundary r hr R N,
        Function.Bijective (singularHillOperator (sourceComplexHminusOne r hr q)-z • singularHillDomainInclusion)) ∧
      ∀ z ∈ sourceCentralSpectrum r hr q N,
        -sourceSpectralBound r hr R-1 < z.re ∧ z.re < freeHillValue N-12*(N:ℝ) ∧
          |z.im| < sourceCentralWindowHeight r hr R N := by
  obtain ⟨N,hN,hcut⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  exact ⟨N,hN,fun q hq => ⟨fun z hz => sourceCentralWindowBoundary_bijective r hr R N hN
    (hcut N le_rfl) q hq z hz,fun z hz => sourceCentralSpectrum_inside_window r hr R q hq N z hz⟩⟩

end NLS.Articles.KdVPseudomeasures
