import NLS.ZakharovShabat.L2WholeLineFloquetInverse

/-! # Identification of physical AC solutions with the original nonreal resolvent -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Matrix Module Complex NLS.FunctionalAnalysis
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- Any global L2 locally AC solution of the physical pencil equation is
the value of the original nonreal resolvent. -/
theorem eq_wholeLineNonrealResolvent_of_AC_solution (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0)
    (f g : WholeLineL2) (F : ℝ → ℂ × ℂ) (he : wholeLineL2Pair f =ᵐ[volume] F)
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b)
    (hp : physicalOperator (l2WholeLinePotential u) F =ᵐ[volume]
      (fun t => z • F t-wholeLineL2Pair g t)) :
    f = wholeLineNonrealResolvent u hu z hz g := by
  have hp' : physicalOperator (l2WholeLinePotential u) F =ᵐ[volume]
      wholeLineL2Pair (z • f-g) := by
    filter_upwards [hp,he,Lp.coeFn_sub (z • f) g,Lp.coeFn_smul z f]
      with t hpt het hsub hsm
    rw [hpt]
    change z • F t-WithLp.ofLp (g t) = WithLp.ofLp ((z • f-g) t)
    simp only [Pi.sub_apply,Pi.smul_apply] at hsub hsm
    rw [hsub,hsm]
    change z • F t-wholeLineL2Pair g t = z • wholeLineL2Pair f t-wholeLineL2Pair g t
    rw [het]
  have hdom : f ∈ (wholeLineMinimalOperator u).closure.domain :=
    (mem_wholeLineMinimalOperator_closure_domain_iff_AC u hu f).mpr
      ⟨F,z • f-g,he,hac,hp'⟩
  have himg : (wholeLineMinimalOperator u).closure ⟨f,hdom⟩ = z • f-g := by
    have h := wholeLineMinimalOperator_adjoint_eq_of_AC_representative
      u hu f (z • f-g) F he hac hp'
    exact ((le_of_eq (wholeLineMinimalOperator_closure_eq_adjoint u hu)).2 rfl).trans h
  have hpencil : wholeLinePencil u z ⟨f,hdom⟩ = g := by
    change z • f-(wholeLineMinimalOperator u).closure ⟨f,hdom⟩ = g
    rw [himg]
    module
  have hi := wholeLineNonrealResolventToDomain_pencil u hu z hz ⟨f,hdom⟩
  rw [hpencil] at hi
  exact (congrArg Subtype.val hi).symm

/-- The previously constructed bounded Floquet inverse is exactly the
original physical resolvent at a nonreal spectral parameter. -/
theorem wholeLineFloquetInverse_eq_nonrealResolvent (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ)
    (h0 : (Complex.log (μ 0)).re ≠ 0) (h1 : (Complex.log (μ 1)).re ≠ 0)
    (C : ℝ) (hC : ∀ t, ‖l2FloquetPeriodicMatrix u z b μ t‖ ≤ C ∧
      ‖(l2FloquetPeriodicMatrix u z b μ t)⁻¹‖ ≤ C) :
    wholeLineFloquetInverse u z b μ h0 h1 C hC = wholeLineNonrealResolvent u hu z hz := by
  apply ContinuousLinearMap.ext
  intro g
  obtain ⟨F,he,hac,hp⟩ := wholeLineFloquetInverse_exists_AC_solution u z b μ h0 h1 C hC g
  exact eq_wholeLineNonrealResolvent_of_AC_solution u hu z hz _ g F he hac hp

end NLS.ZakharovShabat
