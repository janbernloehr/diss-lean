import NLS.KdV.ClassicalHillGreen
import NLS.KdV.ClassicalSourcePrimitive
import NLS.KdV.ClassicalHighGapPairs

/-! # Real Hill branch points and global off-real primitive coverage

The actual scalar Green identity proves that every branch point of a
real continuous potential is a real energy. Consequently the constructed
source primitive covers both entire open energy half-planes at every
such potential. The actual high pairs admit real ordering, also when
the two endpoints coincide, and different high regions are ordered.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- Every actual periodic or antiperiodic scalar energy is real. -/
theorem classicalHillRadicand_energy_im_eq_zero (q : Curve ℂ) (hq : ∀ t, (q t).im = 0)
    (lambda : ℂ) (hzero : classicalHillRadicand (lambda,q) = 0) : lambda.im = 0 := by
  rcases (classicalHillRadicand_eq_zero_iff q lambda).mp hzero with h | h
  · obtain ⟨v,hv,hend⟩ := h
    exact classicalHillFlow_energy_im_eq_zero_of_unit_multiplier q hq lambda 1 (by simp) v hv
      (by simpa only [one_smul] using hend)
  · obtain ⟨v,hv,hend⟩ := h
    exact classicalHillFlow_energy_im_eq_zero_of_unit_multiplier q hq lambda (-1) (by simp) v hv
      (by simpa only [neg_one_smul] using hend)

/-- Both nonreal half-planes lie in the constructed continuation domain
at every real potential, with no spectral cutoff or smallness assumption. -/
theorem mem_classicalHillContinuationDomain_of_im_ne_zero
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda : ℂ) (him : lambda.im ≠ 0) :
    (lambda,q) ∈ classicalHillContinuationDomain := by
  intro s hs
  simp only [sourceSegmentMap,zero_add,sub_zero]
  refine ⟨mem_slitPlane_iff.mpr (Or.inr him),?_⟩
  intro hz
  apply him
  apply classicalHillRadicand_energy_im_eq_zero ((s : ℂ) • q) _ lambda hz
  intro t
  simp only [ContinuousMap.smul_apply,smul_eq_mul,mul_im,ofReal_re,ofReal_im,hq t,
    mul_zero,zero_mul,add_zero]

/-- The free-normalized primitive is analytic on both full nonreal
energy half-planes at every real continuous potential. -/
theorem analyticOnNhd_classicalHillContinuedPrimitive_off_real
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) :
    AnalyticOnNhd ℂ (fun lambda => classicalHillContinuedPrimitive (lambda,q))
      {lambda : ℂ | lambda.im ≠ 0} := by
  intro lambda him
  exact (analyticOnNhd_classicalHillContinuedPrimitive (lambda,q)
    (mem_classicalHillContinuationDomain_of_im_ne_zero q hq lambda him)).comp
    (f := fun lambda : ℂ => (lambda,q)) (analyticAt_id.prod analyticAt_const)

/-- The continued exponential is an actual scalar Floquet multiplier,
not merely a solution of a chosen logarithm equation. -/
theorem exists_classicalHillContinued_floquet_vector
    (t : ℂ × Curve ℂ) (ht : t ∈ classicalHillContinuationDomain) :
    ∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalHillFlow t.2 t.1 v 1 =
      exp (classicalHillContinuedPrimitive t) • v := by
  apply (classicalHill_characteristic_eq_zero_iff t.2 t.1 _).mp
  rw [exp_classicalHillContinuedPrimitive t ht]
  have hp := classicalHillContinuedMultiplier_product t ht
  dsimp only [classicalHillContinuedMultiplier] at hp ⊢
  linear_combination -hp

/-- At real potentials and nonreal energy, the continued primitive never
meets the imaginary axis. This follows from the actual scalar Green
identity rather than from an assumed spectral sheet convention. -/
theorem classicalHillContinuedPrimitive_re_ne_zero_off_real
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda : ℂ) (him : lambda.im ≠ 0) :
    (classicalHillContinuedPrimitive (lambda,q)).re ≠ 0 := by
  intro hre
  obtain ⟨v,hv,hend⟩ := exists_classicalHillContinued_floquet_vector (lambda,q)
    (mem_classicalHillContinuationDomain_of_im_ne_zero q hq lambda him)
  apply him
  exact classicalHillFlow_energy_im_eq_zero_of_unit_multiplier q hq lambda
    (exp (classicalHillContinuedPrimitive (lambda,q))) (by
      rw [norm_exp,hre,Real.exp_zero]) v hv hend

theorem ClassicalHillHighGapPair.im_eq_zero
    {q : Curve ℂ} {n : ℕ+} {l r : ℂ} (h : ClassicalHillHighGapPair q n l r)
    (hq : ∀ t, (q t).im = 0) : l.im = 0 ∧ r.im = 0 :=
  ⟨classicalHillRadicand_energy_im_eq_zero q hq l h.left_zero,
    classicalHillRadicand_energy_im_eq_zero q hq r h.right_zero⟩

/-- The actual high pair can be chosen in real increasing order, with
its existing analytic symmetric data and multiplicities unchanged. -/
theorem exists_ordered_classicalHillHighGapPair_of_counting
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (N : ℕ)
    (h : PeriodicCountingData (by simp) (classicalHillCoefficientPotential q) N)
    (n : ℕ+) (hn : N < (n : ℕ)) :
    ∃ l r : ℂ, ClassicalHillHighGapPair q n l r ∧ l.im = 0 ∧ r.im = 0 ∧ l.re ≤ r.re := by
  obtain ⟨l,r,hpair⟩ := exists_classicalHillHighGapPair_of_counting q N h n hn
  obtain ⟨hl,hr⟩ := hpair.im_eq_zero hq
  by_cases he : l.re ≤ r.re
  · exact ⟨l,r,hpair,hl,hr,he⟩
  · exact ⟨r,l,hpair.swap,hr,hl,le_of_lt (lt_of_not_ge he)⟩

/-- Real points in a high energy region lie in the corresponding
positive squared-frequency interval. -/
theorem classicalHillHighEnergyRegion_real_bounds (n : ℕ+) (lambda : ℂ)
    (hlambda : lambda ∈ classicalHillHighEnergyRegion n) (him : lambda.im = 0) :
    (Real.pi*(n : ℕ)-Real.pi/4)^2 < lambda.re ∧
      lambda.re < (Real.pi*(n : ℕ)+Real.pi/4)^2 := by
  obtain ⟨z,hz,rfl⟩ := hlambda
  have hre := re_pos_of_high_closedBall n n.property z (ball_subset_closedBall hz)
  have hmul : z.re*z.im = 0 := by
    simp only [pow_two,mul_im] at him
    linear_combination him/2
  have hzim : z.im = 0 := (mul_eq_zero.mp hmul).resolve_left hre.ne'
  have hnorm : ‖z-(Real.pi : ℂ)*(n : ℕ)‖ < Real.pi/4 := by
    simpa only [mem_ball,dist_eq_norm] using hz
  have hb : |z.re-Real.pi*(n : ℕ)| < Real.pi/4 := by
    simpa only [sub_re,mul_re,ofReal_re,ofReal_im,natCast_re,natCast_im,
      mul_zero,zero_mul,sub_zero] using (abs_re_le_norm _).trans_lt hnorm
  have hnreal : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
  have hlo : 0 < Real.pi*(n : ℕ)-Real.pi/4 := by nlinarith [Real.pi_pos]
  have hhi : 0 < Real.pi*(n : ℕ)+Real.pi/4 := by positivity
  have hlow : Real.pi*(n : ℕ)-Real.pi/4 < z.re := by linarith [(abs_lt.mp hb).1]
  have hupp : z.re < Real.pi*(n : ℕ)+Real.pi/4 := by linarith [(abs_lt.mp hb).2]
  simp only [pow_two,mul_re,hzim,mul_zero,sub_zero]
  simpa only [pow_two] using
    And.intro ((sq_lt_sq₀ hlo.le hre.le).mpr hlow) ((sq_lt_sq₀ hre.le hhi.le).mpr hupp)

/-- Different positive high energy regions have strictly ordered real
spectral points; in particular adjacent high pairs cannot cross. -/
theorem classicalHillHighEnergyRegion_real_order
    (n m : ℕ+) (hnm : (n : ℕ) < (m : ℕ)) (lambda mu : ℂ)
    (hl : lambda ∈ classicalHillHighEnergyRegion n) (hm : mu ∈ classicalHillHighEnergyRegion m)
    (hli : lambda.im = 0) (hmi : mu.im = 0) : lambda.re < mu.re := by
  have hb1 := classicalHillHighEnergyRegion_real_bounds n lambda hl hli
  have hb2 := classicalHillHighEnergyRegion_real_bounds m mu hm hmi
  have hcast : (n : ℝ)+1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hnm
  have hmreal : (1 : ℝ) ≤ (m : ℕ) := by exact_mod_cast m.property
  have hsep : Real.pi*(n : ℕ)+Real.pi/4 < Real.pi*(m : ℕ)-Real.pi/4 := by
    nlinarith [Real.pi_pos]
  have hpos1 : 0 ≤ Real.pi*(n : ℕ)+Real.pi/4 := by positivity
  have hpos2 : 0 ≤ Real.pi*(m : ℕ)-Real.pi/4 := by nlinarith [Real.pi_pos]
  exact hb1.2.trans (((sq_lt_sq₀ hpos1 hpos2).mpr hsep).trans hb2.1)

theorem ClassicalHillHighGapPair.right_lt_left_of_index_lt
    {q : Curve ℂ} {n m : ℕ+} {l r a b : ℂ}
    (h : ClassicalHillHighGapPair q n l r) (k : ClassicalHillHighGapPair q m a b)
    (hq : ∀ t, (q t).im = 0) (hnm : (n : ℕ) < (m : ℕ)) : r.re < a.re :=
  classicalHillHighEnergyRegion_real_order n m hnm r a h.right_mem k.left_mem
    (h.im_eq_zero hq).2 (k.im_eq_zero hq).1

end NLS.KdV
