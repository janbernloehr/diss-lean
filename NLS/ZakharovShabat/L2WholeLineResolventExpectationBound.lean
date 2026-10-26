import NLS.ZakharovShabat.L2WholeLineLocalResolventBound

/-! # Uniform compact-input expectations of the original physical resolvent -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Complex
open scoped Topology
namespace NLS.ZakharovShabat

/-- The Hermitian fiber pairing is controlled by the two original pair norms. -/
theorem norm_wholeLineVector_inner_le_pair (v w : WholeLineVector) :
    ‖inner ℂ v w‖ ≤ 2*‖v.ofLp‖*‖w.ofLp‖ := by
  calc
    _ ≤ ‖inner ℂ v.ofLp.1 w.ofLp.1‖+‖inner ℂ v.ofLp.2 w.ofLp.2‖ := by
      rw [WithLp.prod_inner_apply]
      exact norm_add_le _ _
    _ = ‖v.ofLp.1‖*‖w.ofLp.1‖+‖v.ofLp.2‖*‖w.ofLp.2‖ := by
      simp [mul_comm]
    _ ≤ ‖v.ofLp‖*‖w.ofLp‖+‖v.ofLp‖*‖w.ofLp‖ := add_le_add
      (mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul (le_max_right _ _) (le_max_right _ _) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- A local pair bound controls the Hilbert expectation against compact forcing. -/
theorem norm_wholeLine_inner_le_of_pair_bound (f g : WholeLineL2) (a c K : ℝ) (hac : a ≤ c)
    (hleft : ∀ᵐ t : ℝ, t ≤ a → wholeLineL2Pair g t = 0)
    (hright : ∀ᵐ t : ℝ, c ≤ t → wholeLineL2Pair g t = 0)
    (hf : ∀ᵐ t : ℝ, t ∈ Icc a c → ‖wholeLineL2Pair f t‖ ≤ K) :
    ‖inner ℂ g f‖ ≤ 2*K*(∫ t in a..c, ‖wholeLineL2Pair g t‖) := by
  have hzero : ∀ᵐ t : ℝ, t ∉ Icc a c → inner ℂ (g t) (f t) = 0 := by
    filter_upwards [hleft,hright] with t hl hr
    intro ht
    have hg : wholeLineL2Pair g t = 0 := by
      by_cases hta : t ≤ a
      · exact hl hta
      · exact hr (le_of_not_ge (fun htc => ht ⟨le_of_not_ge hta,htc⟩))
    have hg' : g t = 0 := (WithLp.linearEquiv 2 ℂ (ℂ × ℂ)).injective hg
    rw [hg',inner_zero_left]
  rw [L2.inner_def,← setIntegral_eq_integral_of_ae_compl_eq_zero hzero]
  have hgint : IntegrableOn (fun t => ‖wholeLineL2Pair g t‖) (Icc a c) volume :=
    (intervalIntegrable_iff').mp (wholeLineL2Pair_norm_intervalIntegrable g a c) |>.mono_set
      (by rw [uIcc_of_le hac])
  calc
    _ ≤ ∫ t in Icc a c, (2*K)*‖wholeLineL2Pair g t‖ := by
      apply MeasureTheory.norm_integral_le_of_norm_le (hgint.const_mul (2*K))
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hf] with t ht
      intro hti
      calc
        _ ≤ 2*‖wholeLineL2Pair g t‖*‖wholeLineL2Pair f t‖ := norm_wholeLineVector_inner_le_pair _ _
        _ ≤ 2*‖wholeLineL2Pair g t‖*K :=
          mul_le_mul_of_nonneg_left (ht hti) (by positivity)
        _ = _ := by ring
    _ = _ := by
      rw [integral_const_mul,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hac]

/-- The compact-input quadratic resolvent bound remains uniform near every
parameter with distinct Floquet roots, including approach to the real line. -/
theorem eventually_norm_wholeLineNonrealResolvent_expectation_le (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z₀ : ℂ)
    (hdisc : (l2Monodromy u z₀).trace^2-4 ≠ 0) (g : WholeLineL2) (a c : ℝ) (hac : a ≤ c)
    (hleft : ∀ᵐ t : ℝ, t ≤ a → wholeLineL2Pair g t = 0)
    (hright : ∀ᵐ t : ℝ, c ≤ t → wholeLineL2Pair g t = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z in 𝓝 z₀, ∀ hz : z.im ≠ 0,
      ‖inner ℂ g (wholeLineNonrealResolvent u hu z hz g)‖ ≤ C := by
  obtain ⟨D,hD,hbound⟩ := eventually_wholeLineNonrealResolvent_pair_bound u hu z₀ hdisc a c
  let m := ∫ t in a..c, ‖wholeLineL2Pair g t‖
  refine ⟨2*D*m^2,by positivity,?_⟩
  filter_upwards [hbound] with z hzbound hz
  have h := norm_wholeLine_inner_le_of_pair_bound
    (wholeLineNonrealResolvent u hu z hz g) g a c (D*m) hac hleft hright
      (hzbound hz g hleft hright)
  convert! h using 1
  dsimp [m]
  ring

end NLS.ZakharovShabat
