import NLS.KdV.ClassicalLocalPrimitive
import NLS.ComplexAnalysis.AnalyticSquareDescent
import NLS.ComplexAnalysis.AnalyticOpenInverse

/-! # Analytic squares of local Hill primitives at branch points

The even function cosh descends through squaring and has a nonzero
derivative in the squared coordinate at zero. Its analytic inverse,
composed with the actual discriminant, constructs a joint analytic
squared primitive at every periodic or antiperiodic branch point. This
does not require a simple spectral zero, so collapsed gaps are included.
Global endpoint normalization and matching along a whole gap remain open.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- The entire even descent of cosh, defined without an analytic root
selection. -/
def squaredCosh (z : ℂ) : ℂ := cosh (Complex.sqrt z)

private theorem sqrt_square (z : ℂ) : (Complex.sqrt z)^2 = z := by
  have h := Complex.cpow_nat_inv_pow z (Nat.succ_ne_zero 1)
  norm_num at h
  simpa only [Complex.sqrt,one_div] using h

@[simp] theorem squaredCosh_sq (z : ℂ) : squaredCosh (z^2) = cosh z := by
  rcases eq_or_eq_neg_of_sq_eq_sq (Complex.sqrt (z^2)) z (sqrt_square (z^2)) with h | h
  · simp only [squaredCosh,h]
  · simp only [squaredCosh,h,cosh_neg]

@[simp] theorem squaredCosh_zero : squaredCosh 0 = 1 := by
  simpa only [zero_pow (by decide : 2 ≠ 0),cosh_zero] using squaredCosh_sq 0

theorem analyticOnNhd_squaredCosh : AnalyticOnNhd ℂ squaredCosh univ := by
  intro z _
  have h : AnalyticAt ℂ (fun w => squaredCosh (w^2)) (Complex.sqrt z) := by
    simpa only [squaredCosh_sq] using (Complex.analyticAt_cosh (x := Complex.sqrt z))
  simpa only [sqrt_square] using
    ComplexAnalysis.analyticAt_of_comp_sq squaredCosh (Complex.sqrt z) h

/-- The derivative in the squared coordinate is exactly one half. -/
theorem hasDerivAt_squaredCosh_zero : HasDerivAt squaredCosh (1/2 : ℂ) 0 := by
  have hEq (z : ℂ) : deriv squaredCosh (z^2)*(2*z) = sinh z := by
    have hd := ((analyticOnNhd_squaredCosh (z^2) (mem_univ _)).differentiableAt.hasDerivAt).comp z
      ((hasDerivAt_id z).pow 2)
    change HasDerivAt (fun w : ℂ => squaredCosh (w^2)) _ z at hd
    have he : (fun w : ℂ => squaredCosh (w^2)) = cosh := funext squaredCosh_sq
    rw [he] at hd
    simpa using hd.unique (Complex.hasDerivAt_cosh z)
  have hdg : AnalyticAt ℂ (deriv squaredCosh) 0 :=
    (analyticOnNhd_squaredCosh 0 (mem_univ _)).deriv
  have hsq0 : HasDerivAt (fun z : ℂ => z^2) 0 0 := by
    simpa using! (hasDerivAt_id (0 : ℂ)).pow 2
  have hg0 : HasDerivAt (deriv squaredCosh) (deriv (deriv squaredCosh) 0) ((0 : ℂ)^2) := by
    simpa using hdg.differentiableAt.hasDerivAt
  have hleft := (hg0.comp (h := fun z : ℂ => z^2) 0 hsq0).mul
    ((hasDerivAt_id (0 : ℂ)).const_mul 2)
  change HasDerivAt (fun z : ℂ => deriv squaredCosh (z^2)*(2*z)) _ 0 at hleft
  have he : (fun z : ℂ => deriv squaredCosh (z^2)*(2*z)) = sinh := funext hEq
  rw [he] at hleft
  have hn : deriv squaredCosh 0 * 2 = 1 := by
    simpa using hleft.unique (Complex.hasDerivAt_sinh 0)
  have hval : deriv squaredCosh 0 = (1/2 : ℂ) := by
    linear_combination hn/2
  rw [← hval]
  exact (analyticOnNhd_squaredCosh 0 (mem_univ _)).differentiableAt.hasDerivAt

/-- An inverse for the squared primitive coordinate near the normalized
value cosh(0)=1, on actual complex open neighborhoods. -/
theorem exists_squaredCosh_inverse :
    ∃ U W : Set ℂ, IsOpen U ∧ IsOpen W ∧ 0 ∈ U ∧ 1 ∈ W ∧
      ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G W ∧ G 1 = 0 ∧
        (∀ z ∈ U, G (squaredCosh z) = z) ∧
        (∀ y ∈ W, G y ∈ U ∧ squaredCosh (G y) = y) := by
  have hu : IsUnit (fderiv ℂ squaredCosh 0) := by
    rw [hasDerivAt_squaredCosh_zero.hasFDerivAt.fderiv,
      ContinuousLinearMap.isUnit_iff_bijective]
    change Function.Bijective (fun z : ℂ => z * (1/2 : ℂ))
    have hb := (LinearEquiv.smulOfNeZero ℂ ℂ (1/2) (by norm_num)).bijective
    change Function.Bijective (fun z : ℂ => (1/2 : ℂ) • z) at hb
    simpa only [smul_eq_mul,mul_comm] using hb
  obtain ⟨U,W,hU,hW,h0,h1,_,_,_,G,_,hG,hleft,hright⟩ :=
    ComplexAnalysis.exists_analytic_inverse_open_sets isOpen_univ analyticOnNhd_squaredCosh
      (mem_univ 0) hu
  refine ⟨U,W,hU,hW,h0,?_,G,hG,?_,hleft,hright⟩
  · simpa only [squaredCosh_zero] using h1
  · simpa only [squaredCosh_zero] using hleft 0 h0

/-- At either sign of the periodic/antiperiodic trace, the square of the
small normalized primitive is jointly analytic in energy and potential.
No condition on the order of the spectral zero is imposed. -/
theorem exists_classicalHill_local_squared_primitive
    (p : ℂ × NLS.LinearVolterra.Curve ℂ) (σ : ℂ) (hσ : σ^2 = 1)
    (hbase : classicalHillDiscriminant p.2 p.1 = 2*σ) :
    ∃ V : Set (ℂ × NLS.LinearVolterra.Curve ℂ), IsOpen V ∧ p ∈ V ∧
      ∃ U : Set ℂ, IsOpen U ∧ 0 ∈ U ∧
        ∃ K : ℂ × NLS.LinearVolterra.Curve ℂ → ℂ,
          AnalyticOnNhd ℂ K V ∧ K p = 0 ∧
          (∀ a ∈ V, K a ∈ U ∧ squaredCosh (K a) = σ*classicalHillDiscriminant a.2 a.1/2) ∧
          ∀ a ∈ V, ∀ z : ℂ, z^2 ∈ U →
            2*cosh z = σ*classicalHillDiscriminant a.2 a.1 → K a = z^2 := by
  obtain ⟨U,W,hU,hW,h0,h1,G,hG,hG1,hleft,hright⟩ := exists_squaredCosh_inverse
  let D : ℂ × NLS.LinearVolterra.Curve ℂ → ℂ :=
    fun a => σ*classicalHillDiscriminant a.2 a.1/2
  have hD : AnalyticOnNhd ℂ D univ :=
    (analyticOnNhd_const.mul analyticOnNhd_classicalHillDiscriminant_joint).div_const
  have hDp : D p = 1 := by
    dsimp only [D]
    rw [hbase]
    linear_combination hσ
  let V := D ⁻¹' W
  have hV : IsOpen V := hW.preimage hD.continuous
  have hpV : p ∈ V := by change D p ∈ W; rwa [hDp]
  let K := G ∘ D
  have hK : AnalyticOnNhd ℂ K V := by
    intro a ha
    exact (hG (D a) ha).comp (hD a (mem_univ _))
  refine ⟨V,hV,hpV,U,hU,h0,K,hK,?_,?_,?_⟩
  · change G (D p) = 0
    rw [hDp,hG1]
  · intro a ha
    exact hright (D a) ha
  intro a _ z hz htrace
  have he : D a = squaredCosh (z^2) := by
    rw [squaredCosh_sq]
    dsimp only [D]
    linear_combination -htrace/2
  change G (D a) = z^2
  rw [he]
  exact hleft (z^2) hz

end NLS.KdV
