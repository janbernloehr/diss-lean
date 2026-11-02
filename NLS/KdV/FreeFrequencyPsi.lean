import NLS.KdV.ClassicalFreePrimitive
import NLS.KdV.FrequencyMoments
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! # Actual free normalized differentials for the KdV frequency moments

The entire numerator is constructed as a divided difference of the actual
free Hill discriminant derivative. Its apparent singularity at the omitted
mode is filled analytically, rather than assigned the value of total division.
The periods use the actual root sheet of the free-normalized Hill primitive.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- The source free periodic/antiperiodic energy of a positive Hill mode. -/
def freeHillEnergy (n : ℕ+) : ℂ := ((((n : ℝ)*Real.pi)^2 : ℝ) : ℂ)

theorem sqrt_freeHillEnergy (n : ℕ+) :
    Complex.sqrt (freeHillEnergy n) = (n : ℂ)*Real.pi := by
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast n.pos.le
  rw [freeHillEnergy, Complex.sqrt_of_nonneg (by exact_mod_cast sq_nonneg ((n : ℝ)*Real.pi))]
  simp only [ofReal_re, Real.sqrt_sq (mul_nonneg hn Real.pi_pos.le)]
  norm_cast

theorem freeHillEnergy_mem_slitPlane (n : ℕ+) : freeHillEnergy n ∈ slitPlane := by
  apply Or.inl
  change (0 : ℝ) < ((n : ℝ)*Real.pi)^2
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  positivity

theorem freeHillEnergy_injective : Function.Injective freeHillEnergy := by
  intro n k h
  have he : ((n : ℝ)*Real.pi)^2 = ((k : ℝ)*Real.pi)^2 := congrArg re h
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hk : (0 : ℝ) < k := by exact_mod_cast k.pos
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ he with he | he
  · have hnk : (n : ℝ) = k := mul_right_cancel₀ Real.pi_ne_zero he
    exact_mod_cast hnk
  · nlinarith [mul_pos hn Real.pi_pos, mul_pos hk Real.pi_pos]

private theorem hasDerivAt_sqrt_inv (lam : ℂ) (hlam : lam ∈ slitPlane) :
    HasDerivAt Complex.sqrt ((Complex.sqrt lam)⁻¹/2) lam := by
  have he : lam^(-1/2 : ℂ) = (Complex.sqrt lam)⁻¹ := by
    rw [show (-1/2 : ℂ) = -(2⁻¹) by norm_num, Complex.cpow_neg]
    rfl
  simpa only [he] using Complex.hasDerivAt_sqrt hlam

theorem hasDerivAt_classicalHillDiscriminant_free (lam : ℂ) (hlam : lam ∈ slitPlane) :
    HasDerivAt (classicalHillDiscriminant 0)
      (-sin (Complex.sqrt lam)/Complex.sqrt lam) lam := by
  have he : classicalHillDiscriminant 0 = (fun z => 2*cos (Complex.sqrt z)) :=
    funext classicalHillDiscriminant_zero
  rw [he]
  convert ((Complex.hasDerivAt_cos (Complex.sqrt lam)).comp lam
    (hasDerivAt_sqrt_inv lam hlam)).const_mul 2 using 1 <;> first | rfl | ring

theorem deriv_classicalHillDiscriminant_free_energy (n : ℕ+) :
    deriv (classicalHillDiscriminant 0) (freeHillEnergy n) = 0 := by
  rw [(hasDerivAt_classicalHillDiscriminant_free _ (freeHillEnergy_mem_slitPlane n)).deriv,
    sqrt_freeHillEnergy]
  simpa using congrArg (fun z : ℂ => -z/((n : ℂ)*Real.pi)) (Complex.sin_nat_mul_pi (n : ℕ))

theorem cos_sqrt_freeHillEnergy (n : ℕ+) :
    cos (Complex.sqrt (freeHillEnergy n)) = (-1 : ℂ)^(n : ℕ) := by
  rw [sqrt_freeHillEnergy]
  have he := congrArg Complex.ofReal (Real.cos_nat_mul_pi (n : ℕ))
  push_cast at he
  exact he

/-- The entire free psi numerator, normalized for the `2π δ_nk` periods. -/
def classicalHillFreePsi (n : ℕ+) (lam : ℂ) : ℂ :=
  (2*(n : ℂ)*Real.pi)*dslope (deriv (classicalHillDiscriminant 0)) (freeHillEnergy n) lam

theorem analyticOnNhd_classicalHillFreePsi (n : ℕ+) :
    AnalyticOnNhd ℂ (classicalHillFreePsi n) univ := by
  have hd : AnalyticOnNhd ℂ (deriv (classicalHillDiscriminant 0)) univ := by
    intro z _
    exact (analyticOnNhd_classicalHillDiscriminant 0 z (mem_univ _)).deriv
  have hs : DifferentiableOn ℂ
      (dslope (deriv (classicalHillDiscriminant 0)) (freeHillEnergy n)) univ :=
    (Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ 𝓝 (freeHillEnergy n))).mpr
      hd.differentiableOn
  exact analyticOnNhd_const.mul (hs.analyticOnNhd isOpen_univ)

theorem classicalHillFreePsi_factor (n : ℕ+) (lam : ℂ) :
    (lam-freeHillEnergy n)*classicalHillFreePsi n lam =
      (2*(n : ℂ)*Real.pi)*deriv (classicalHillDiscriminant 0) lam := by
  have hs := sub_smul_dslope (deriv (classicalHillDiscriminant 0)) (freeHillEnergy n) lam
  rw [deriv_classicalHillDiscriminant_free_energy, sub_zero, smul_eq_mul] at hs
  dsimp only [classicalHillFreePsi]
  linear_combination (2*(n : ℂ)*Real.pi)*hs

/-- The actual free critical points are simple zeros of the discriminant
derivative. This is the nondegeneracy needed to deform the numerator basis. -/
theorem deriv_deriv_classicalHillDiscriminant_free_energy (n : ℕ+) :
    deriv (deriv (classicalHillDiscriminant 0)) (freeHillEnergy n) =
      -((-1 : ℂ)^(n : ℕ))/(2*((n : ℂ)*Real.pi)^2) := by
  let a := freeHillEnergy n
  have ha := freeHillEnergy_mem_slitPlane n
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsqrt : Complex.sqrt a ≠ 0 := by
    dsimp only [a]
    rw [sqrt_freeHillEnergy]
    exact mul_ne_zero hn hpi
  have hsq := hasDerivAt_sqrt_inv a ha
  have hd := (((Complex.hasDerivAt_sin (Complex.sqrt a)).comp a hsq).neg).div hsq hsqrt
  have he : deriv (classicalHillDiscriminant 0) =ᶠ[𝓝 a]
      (fun z => -sin (Complex.sqrt z)/Complex.sqrt z) := by
    filter_upwards [isOpen_slitPlane.mem_nhds ha] with z hz
    exact (hasDerivAt_classicalHillDiscriminant_free z hz).deriv
  have hder := (hd.congr_of_eventuallyEq he).deriv
  change deriv (deriv (classicalHillDiscriminant 0)) a = _
  rw [hder]
  dsimp only [a, Function.comp_def, Pi.neg_apply]
  rw [sqrt_freeHillEnergy, Complex.sin_nat_mul_pi]
  have hcos := cos_sqrt_freeHillEnergy n
  rw [sqrt_freeHillEnergy] at hcos
  rw [hcos]
  field_simp [hn, hpi]
  ring

theorem deriv_deriv_classicalHillDiscriminant_free_energy_ne_zero (n : ℕ+) :
    deriv (deriv (classicalHillDiscriminant 0)) (freeHillEnergy n) ≠ 0 := by
  rw [deriv_deriv_classicalHillDiscriminant_free_energy]
  exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num)))
    (mul_ne_zero (by norm_num) (pow_ne_zero _ (mul_ne_zero
      (by exact_mod_cast n.ne_zero) (by exact_mod_cast Real.pi_ne_zero))))

/-- At the omitted energy the numerator has its actual nonzero analytic
value, rather than the zero produced by total division. -/
theorem classicalHillFreePsi_energy (n : ℕ+) :
    classicalHillFreePsi n (freeHillEnergy n) = -((-1 : ℂ)^(n : ℕ))/((n : ℂ)*Real.pi) := by
  rw [classicalHillFreePsi, dslope_same, deriv_deriv_classicalHillDiscriminant_free_energy]
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hn, hpi]

theorem classicalHillFreePsi_energy_ne_zero (n : ℕ+) :
    classicalHillFreePsi n (freeHillEnergy n) ≠ 0 := by
  rw [classicalHillFreePsi_energy]
  exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num)))
    (mul_ne_zero (by exact_mod_cast n.ne_zero) (by exact_mod_cast Real.pi_ne_zero))

theorem classicalHillFreePsi_other_energy (n k : ℕ+) (hnk : n ≠ k) :
    classicalHillFreePsi n (freeHillEnergy k) = 0 := by
  have he := classicalHillFreePsi_factor n (freeHillEnergy k)
  rw [deriv_classicalHillDiscriminant_free_energy, mul_zero] at he
  have hne : freeHillEnergy k ≠ freeHillEnergy n :=
    fun h => hnk (freeHillEnergy_injective h.symm)
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne)

theorem classicalHillFreeRoot_eq_sin (lam : ℂ) :
    classicalHillFreeRoot lam = -2*I*sin (Complex.sqrt lam) := by
  simp only [classicalHillFreeRoot, classicalHillFreePrimitive, neg_mul, sinh_neg]
  rw [mul_comm I, sinh_mul_I]
  ring

theorem classicalHillFreeRoot_energy (n : ℕ+) : classicalHillFreeRoot (freeHillEnergy n) = 0 := by
  rw [classicalHillFreeRoot_eq_sin, sqrt_freeHillEnergy, Complex.sin_nat_mul_pi]
  ring

theorem hasDerivAt_classicalHillFreeRoot (lam : ℂ) (hlam : lam ∈ slitPlane) :
    HasDerivAt classicalHillFreeRoot (-I*cos (Complex.sqrt lam)/Complex.sqrt lam) lam := by
  rw [show classicalHillFreeRoot = (fun z => -2*I*sin (Complex.sqrt z)) from
    funext classicalHillFreeRoot_eq_sin]
  convert ((Complex.hasDerivAt_sin (Complex.sqrt lam)).comp lam
    (hasDerivAt_sqrt_inv lam hlam)).const_mul (-2*I) using 1 <;> first | rfl | ring

theorem deriv_classicalHillFreeRoot_energy_ne_zero (n : ℕ+) :
    deriv classicalHillFreeRoot (freeHillEnergy n) ≠ 0 := by
  rw [(hasDerivAt_classicalHillFreeRoot _ (freeHillEnergy_mem_slitPlane n)).deriv,
    sqrt_freeHillEnergy]
  have hcos := cos_sqrt_freeHillEnergy n
  rw [sqrt_freeHillEnergy] at hcos
  rw [hcos]
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
    (pow_ne_zero _ (by norm_num))) (mul_ne_zero (by exact_mod_cast n.ne_zero)
      (by exact_mod_cast Real.pi_ne_zero))

/-- Each positive free mode has an actual isolating disc in the energy
slit plane. Nonvanishing off its center is proved from the simple zero
of the constructed root; no spectral isolation is assumed. -/
theorem exists_freeHill_isolating_disc (n : ℕ+) :
    ∃ R : ℝ, 0 < R ∧ closedBall (freeHillEnergy n) R ⊆ slitPlane ∧
      ∀ z ∈ closedBall (freeHillEnergy n) R, z ≠ freeHillEnergy n →
        classicalHillFreeRoot z ≠ 0 := by
  have hd := hasDerivAt_classicalHillFreeRoot _ (freeHillEnergy_mem_slitPlane n)
  have hc : ContinuousAt (dslope classicalHillFreeRoot (freeHillEnergy n)) (freeHillEnergy n) :=
    continuousAt_dslope_same.mpr hd.differentiableAt
  have hne : dslope classicalHillFreeRoot (freeHillEnergy n) (freeHillEnergy n) ≠ 0 := by
    simpa only [dslope_same] using deriv_classicalHillFreeRoot_energy_ne_zero n
  have hgood : ∀ᶠ z in 𝓝 (freeHillEnergy n), z ∈ slitPlane ∧
      dslope classicalHillFreeRoot (freeHillEnergy n) z ≠ 0 := by
    filter_upwards [isOpen_slitPlane.mem_nhds (freeHillEnergy_mem_slitPlane n),
      hc.eventually_ne hne] with z hz hdz
    exact ⟨hz, hdz⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hsub : closedBall (freeHillEnergy n) (δ/2) ⊆ ball (freeHillEnergy n) δ :=
    closedBall_subset_ball (by linarith)
  refine ⟨δ/2, by positivity, fun z hz => (hball (hsub hz)).1, ?_⟩
  intro z hz hzn hzroot
  have he := sub_smul_dslope classicalHillFreeRoot (freeHillEnergy n) z
  rw [classicalHillFreeRoot_energy, hzroot, sub_zero, smul_eq_mul] at he
  exact (mul_ne_zero (sub_ne_zero.mpr hzn) (hball (hsub hz)).2) he

theorem classicalHillFreePsi_div_root (n : ℕ+) (lam : ℂ) (hlam : lam ∈ slitPlane)
    (hne : lam ≠ freeHillEnergy n) (hr : classicalHillFreeRoot lam ≠ 0) :
    classicalHillFreePsi n lam/classicalHillFreeRoot lam =
      (-I*(n : ℂ)*Real.pi/Complex.sqrt lam)/(lam-freeHillEnergy n) := by
  have hs : sin (Complex.sqrt lam) ≠ 0 := by
    intro h
    apply hr
    simp only [classicalHillFreeRoot_eq_sin, h, mul_zero]
  have hf := classicalHillFreePsi_factor n lam
  rw [(hasDerivAt_classicalHillDiscriminant_free lam hlam).deriv] at hf
  have hcoeff : classicalHillFreePsi n lam =
      ((2*(n : ℂ)*Real.pi)*(-sin (Complex.sqrt lam)/Complex.sqrt lam))/(lam-freeHillEnergy n) :=
    (eq_div_iff (sub_ne_zero.mpr hne)).mpr (by simpa only [mul_comm] using hf)
  rw [hcoeff, classicalHillFreeRoot_eq_sin]
  field_simp [hs, I_ne_zero]
  simp only [I_sq]
  ring

private theorem analytic_freePsi_residue (n : ℕ+) :
    AnalyticOnNhd ℂ (fun z => -I*(n : ℂ)*Real.pi/Complex.sqrt z) slitPlane := by
  intro z hz
  have hs : AnalyticAt ℂ Complex.sqrt z :=
    Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds hz)
  exact analyticAt_const.div hs
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero hz)))

/-- The actual free differential has the exact diagonal period `2π`. -/
theorem circleIntegral_classicalHillFreePsi_diagonal
    (n : ℕ+) (R : ℝ) (hR : 0 < R)
    (hdisc : closedBall (freeHillEnergy n) R ⊆ slitPlane)
    (hroot : ∀ z ∈ sphere (freeHillEnergy n) R, classicalHillFreeRoot z ≠ 0) :
    (∮ z in C(freeHillEnergy n,R), classicalHillFreePsi n z/classicalHillFreeRoot z) =
      2*Real.pi := by
  have ha := (analytic_freePsi_residue n).mono hdisc
  calc
    _ = ∮ z in C(freeHillEnergy n,R),
        (z-freeHillEnergy n)⁻¹ • (-I*(n : ℂ)*Real.pi/Complex.sqrt z) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hne : z ≠ freeHillEnergy n := sphere_disjoint_ball.ne_of_mem hz (mem_ball_self hR)
      simpa only [smul_eq_mul, div_eq_inv_mul] using
        classicalHillFreePsi_div_root n z (hdisc (sphere_subset_closedBall hz)) hne (hroot z hz)
    _ = (2*Real.pi*I)*(-I*(n : ℂ)*Real.pi/Complex.sqrt (freeHillEnergy n)) := by
      exact ha.differentiableOn.circleIntegral_sub_inv_smul (mem_ball_self hR)
    _ = 2*Real.pi := by
      rw [sqrt_freeHillEnergy]
      have hn : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp [hn, hpi]
      simp only [I_sq]
      ring

/-- Away from its omitted energy the actual free differential has zero
period, even when the enclosed free root itself vanishes. -/
theorem circleIntegral_classicalHillFreePsi_offDiagonal
    (n : ℕ+) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hdisc : closedBall c R ⊆ slitPlane)
    (hout : freeHillEnergy n ∉ closedBall c R)
    (hroot : ∀ z ∈ sphere c R, classicalHillFreeRoot z ≠ 0) :
    (∮ z in C(c,R), classicalHillFreePsi n z/classicalHillFreeRoot z) = 0 := by
  have ha : AnalyticOnNhd ℂ
      (fun z => (-I*(n : ℂ)*Real.pi/Complex.sqrt z)/(z-freeHillEnergy n)) (closedBall c R) := by
    apply ((analytic_freePsi_residue n).mono hdisc).div (analyticOnNhd_id.sub analyticOnNhd_const)
    intro z hz
    apply sub_ne_zero.mpr
    change z ≠ freeHillEnergy n
    intro h
    exact hout (h ▸ hz)
  calc
    _ = ∮ z in C(c,R), (-I*(n : ℂ)*Real.pi/Complex.sqrt z)/(z-freeHillEnergy n) := by
      apply circleIntegral.integral_congr hR
      intro z hz
      exact classicalHillFreePsi_div_root n z (hdisc (sphere_subset_closedBall hz))
        (fun h => hout (h ▸ sphere_subset_closedBall hz)) (hroot z hz)
    _ = 0 := circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
      ha.continuousOn (fun z hz => (ha z (ball_subset_closedBall hz.1)).differentiableAt)

/-- One isolating circle for each free gap normalizes all the entire
free differentials simultaneously, with the source's exact `2π δ_nk`. -/
theorem exists_classicalHillFreePsi_periods (k : ℕ+) :
    ∃ R : ℝ, 0 < R ∧ closedBall (freeHillEnergy k) R ⊆ slitPlane ∧
      (∀ z ∈ sphere (freeHillEnergy k) R, classicalHillFreeRoot z ≠ 0) ∧
      (∀ n : ℕ+, n ≠ k → freeHillEnergy n ∉ closedBall (freeHillEnergy k) R) ∧
      ∀ n : ℕ+, (∮ z in C(freeHillEnergy k,R),
        classicalHillFreePsi n z/classicalHillFreeRoot z) = if n = k then 2*Real.pi else 0 := by
  obtain ⟨R, hR, hdisc, hiso⟩ := exists_freeHill_isolating_disc k
  have hroot (z : ℂ) (hz : z ∈ sphere (freeHillEnergy k) R) : classicalHillFreeRoot z ≠ 0 :=
    hiso z (sphere_subset_closedBall hz) (sphere_disjoint_ball.ne_of_mem hz (mem_ball_self hR))
  have hout (n : ℕ+) (hnk : n ≠ k) : freeHillEnergy n ∉ closedBall (freeHillEnergy k) R := by
    intro hn
    have hne : freeHillEnergy n ≠ freeHillEnergy k :=
      fun h => hnk (freeHillEnergy_injective h)
    exact hiso _ hn hne (classicalHillFreeRoot_energy n)
  refine ⟨R, hR, hdisc, hroot, hout, ?_⟩
  intro n
  by_cases hnk : n = k
  · subst n
    simpa using circleIntegral_classicalHillFreePsi_diagonal k R hR hdisc hroot
  · simp only [if_neg hnk]
    exact circleIntegral_classicalHillFreePsi_offDiagonal n (freeHillEnergy k) R hR.le hdisc
      (hout n hnk) hroot

/-- The source shift of the actual free primitive vanishes at its own gap. -/
def classicalHillFreeGapPrimitive (k : ℕ+) (lam : ℂ) : ℂ :=
  classicalHillFreePrimitive lam+I*(k : ℂ)*Real.pi

theorem classicalHillFreeGapPrimitive_energy (k : ℕ+) :
    classicalHillFreeGapPrimitive k (freeHillEnergy k) = 0 := by
  rw [classicalHillFreeGapPrimitive, classicalHillFreePrimitive, sqrt_freeHillEnergy]
  ring

theorem analyticOnNhd_classicalHillFreeGapPrimitive (k : ℕ+) :
    AnalyticOnNhd ℂ (classicalHillFreeGapPrimitive k) slitPlane :=
  analyticOnNhd_classicalHillFreePrimitive.add analyticOnNhd_const

/-- Every positive weighted moment vanishes on a free collapsed gap, for
every output index, including the diagonal differential with a pole. -/
theorem classicalHillFreePsi_positive_moment_eq_zero
    (n k : ℕ+) (R : ℝ) (hR : 0 < R)
    (hdisc : closedBall (freeHillEnergy k) R ⊆ slitPlane)
    (hroot : ∀ z ∈ sphere (freeHillEnergy k) R, classicalHillFreeRoot z ≠ 0)
    (hout : n ≠ k → freeHillEnergy n ∉ closedBall (freeHillEnergy k) R) (m : ℕ) :
    frequencyMoment (classicalHillFreeGapPrimitive k)
      (fun z => classicalHillFreePsi n z/classicalHillFreeRoot z) (freeHillEnergy k) R (m+1) = 0 := by
  let F := classicalHillFreeGapPrimitive k
  let A := fun z => -I*(n : ℂ)*Real.pi/Complex.sqrt z
  have hF := (analyticOnNhd_classicalHillFreeGapPrimitive k).mono hdisc
  have hA := (analytic_freePsi_residue n).mono hdisc
  have heq : frequencyMoment F (fun z => classicalHillFreePsi n z/classicalHillFreeRoot z)
      (freeHillEnergy k) R (m+1) =
      ∮ z in C(freeHillEnergy k,R), (F z^(m+1)*A z)/(z-freeHillEnergy n) := by
    unfold frequencyMoment
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hne : z ≠ freeHillEnergy n := by
      by_cases hnk : n = k
      · subst n
        exact sphere_disjoint_ball.ne_of_mem hz (mem_ball_self hR)
      · exact fun h => hout hnk (h ▸ sphere_subset_closedBall hz)
    change F z^(m+1)*(classicalHillFreePsi n z/classicalHillFreeRoot z) = _
    rw [classicalHillFreePsi_div_root n z (hdisc (sphere_subset_closedBall hz)) hne (hroot z hz)]
    dsimp only [A]
    ring
  rw [heq]
  by_cases hnk : n = k
  · subst n
    have hi := ((hF.pow (m+1)).mul hA).differentiableOn.circleIntegral_sub_inv_smul
      (mem_ball_self hR)
    simp only [smul_eq_mul, ← div_eq_inv_mul] at hi
    change (∮ z in C(freeHillEnergy k,R), (F z^(m+1)*A z)/(z-freeHillEnergy k)) =
      (2*Real.pi*I)*(F (freeHillEnergy k)^(m+1)*A (freeHillEnergy k)) at hi
    rw [hi]
    simp only [F, classicalHillFreeGapPrimitive_energy, zero_pow (Nat.succ_ne_zero m),
      zero_mul, mul_zero]
  · have ha : AnalyticOnNhd ℂ (fun z => (F z^(m+1)*A z)/(z-freeHillEnergy n))
        (closedBall (freeHillEnergy k) R) := by
      apply ((hF.pow (m+1)).mul hA).div (analyticOnNhd_id.sub analyticOnNhd_const)
      intro z hz
      apply sub_ne_zero.mpr
      change z ≠ freeHillEnergy n
      intro h
      exact hout hnk (h ▸ hz)
    exact circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le countable_empty
      ha.continuousOn (fun z hz => (ha z (ball_subset_closedBall hz.1)).differentiableAt)

/-- An actual choice of positive isolating radius for every free Hill gap. -/
def classicalHillFreeFrequencyRadius (k : ℕ+) : ℝ :=
  Classical.choose (exists_classicalHillFreePsi_periods k)

/-- Literal free frequency moments, using the constructed numerator, actual
root sheet, source shift and a proved isolating contour. -/
def classicalHillFreeFrequencyMoment (n k : ℕ+) (m : ℕ) : ℂ :=
  frequencyMoment (classicalHillFreeGapPrimitive k)
    (fun z => classicalHillFreePsi n z/classicalHillFreeRoot z)
    (freeHillEnergy k) (classicalHillFreeFrequencyRadius k) m

theorem classicalHillFreeFrequencyMoment_zeroth (n k : ℕ+) :
    classicalHillFreeFrequencyMoment n k 0 = if n = k then (2*Real.pi : ℂ) else 0 := by
  have h := (Classical.choose_spec (exists_classicalHillFreePsi_periods k)).2.2.2.2 n
  by_cases hnk : n = k <;>
    simpa [classicalHillFreeFrequencyMoment, classicalHillFreeFrequencyRadius,
      frequencyMoment, hnk] using h

theorem classicalHillFreeFrequencyMoment_positive (n k : ℕ+) (m : ℕ) :
    classicalHillFreeFrequencyMoment n k (m+1) = 0 := by
  obtain ⟨hR, hdisc, hroot, hout, _⟩ :=
    Classical.choose_spec (exists_classicalHillFreePsi_periods k)
  exact classicalHillFreePsi_positive_moment_eq_zero n k _ hR hdisc hroot (hout n) m

end NLS.KdV
