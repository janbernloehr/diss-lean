import NLS.ZakharovShabat.AKNSConjugation

/-! # Real and imaginary decomposition of the full classical AKNS operator -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace NLS.ZakharovShabat

def aknsRealVector (u : ℂ × ℂ) : ℂ × ℂ := ((u.1.re : ℂ),(u.2.re : ℂ))
def aknsImagVector (u : ℂ × ℂ) : ℂ × ℂ := ((u.1.im : ℂ),(u.2.im : ℂ))

theorem aknsRealVector_eq (u : ℂ × ℂ) :
    aknsRealVector u = (1/2 : ℂ) • u+(1/2 : ℂ) • star u := by
  apply Prod.ext <;> apply Complex.ext <;> simp [aknsRealVector,Prod.star_def,smul_eq_mul] <;> ring

theorem aknsImagVector_eq (u : ℂ × ℂ) :
    aknsImagVector u = (-Complex.I/2) • u+(Complex.I/2) • star u := by
  apply Prod.ext <;> apply Complex.ext <;> simp [aknsImagVector,Prod.star_def,smul_eq_mul] <;> ring

theorem aknsRealVector_add_I_imag (u : ℂ × ℂ) :
    aknsRealVector u+Complex.I • aknsImagVector u = u := by
  apply Prod.ext <;> apply Complex.ext <;> simp [aknsRealVector,aknsImagVector,smul_eq_mul]

/-- Taking real parts retains the full original H1 regularity and both endpoint conditions. -/
theorem HasAKNSIntervalDomain.realPart {b : BoundaryCondition} {g : ℝ → ℂ × ℂ}
    (hg : HasAKNSIntervalDomain b g) : HasAKNSIntervalDomain b (fun x => aknsRealVector (g x)) := by
  simpa only [aknsRealVector_eq] using hg.linearCombination hg.conj (1/2 : ℂ) (1/2 : ℂ)

/-- Taking imaginary parts also retains the same full classical boundary domain. -/
theorem HasAKNSIntervalDomain.imagPart {b : BoundaryCondition} {g : ℝ → ℂ × ℂ}
    (hg : HasAKNSIntervalDomain b g) : HasAKNSIntervalDomain b (fun x => aknsImagVector (g x)) := by
  simpa only [aknsImagVector_eq] using hg.linearCombination hg.conj (-Complex.I/2) (Complex.I/2)

/-- The physical differential expression is complex linear on the full domain. -/
theorem aknsPhysicalOperator_linearCombination {b : BoundaryCondition} {f g : ℝ → ℂ × ℂ}
    (hf : HasAKNSIntervalDomain b f) (hg : HasAKNSIntervalDomain b g)
    (q p : ℝ → ℂ) (a c : ℂ) :
    aknsPhysicalOperator q p (fun x => a • f x+c • g x)
      =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => a • aknsPhysicalOperator q p f x+c • aknsPhysicalOperator q p g x) := by
  filter_upwards [hf.fst_regular.ae_differentiableAt,hf.snd_regular.ae_differentiableAt,
    hg.fst_regular.ae_differentiableAt,hg.snd_regular.ae_differentiableAt] with x hf1 hf2 hg1 hg2
  have hd1 := ((hf1.hasDerivAt.const_mul a).add (hg1.hasDerivAt.const_mul c)).deriv
  have hd2 := ((hf2.hasDerivAt.const_mul a).add (hg2.hasDerivAt.const_mul c)).deriv
  simp only [Pi.add_def] at hd1 hd2
  change aknsAction (q x) (p x) (a • f x+c • g x)
    (deriv (fun t => a*(f t).1+c*(g t).1) x,deriv (fun t => a*(f t).2+c*(g t).2) x) = _
  rw [hd1,hd2]
  ext <;> simp [aknsPhysicalOperator,aknsAction,smul_eq_mul] <;> ring

/-- The original complex domain and its actual action decompose into real and
imaginary domain functions. No smooth extension beyond the interval is assumed. -/
theorem aknsPhysicalOperator_decomposition {b : BoundaryCondition} {g : ℝ → ℂ × ℂ}
    (hg : HasAKNSIntervalDomain b g) (q p : ℝ → ℂ) :
    HasAKNSIntervalDomain b (fun x => aknsRealVector (g x)) ∧
    HasAKNSIntervalDomain b (fun x => aknsImagVector (g x)) ∧
    (∀ x, g x = aknsRealVector (g x)+Complex.I • aknsImagVector (g x)) ∧
    aknsPhysicalOperator q p g =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => aknsPhysicalOperator q p (fun t => aknsRealVector (g t)) x+
        Complex.I • aknsPhysicalOperator q p (fun t => aknsImagVector (g t)) x) := by
  refine ⟨hg.realPart,hg.imagPart,fun x => (aknsRealVector_add_I_imag (g x)).symm,?_⟩
  simpa only [one_smul,aknsRealVector_add_I_imag] using
    aknsPhysicalOperator_linearCombination hg.realPart hg.imagPart q p 1 Complex.I

/-- For real potentials the two summands in the complexification have real outputs. -/
theorem aknsPhysicalOperator_real_parts (q p : ℝ → ℝ) (g : ℝ → ℂ × ℂ) (x : ℝ) :
    star (aknsPhysicalOperator (fun t => (q t : ℂ)) (fun t => (p t : ℂ))
      (fun t => aknsRealVector (g t)) x) =
      aknsPhysicalOperator (fun t => (q t : ℂ)) (fun t => (p t : ℂ))
        (fun t => aknsRealVector (g t)) x ∧
    star (aknsPhysicalOperator (fun t => (q t : ℂ)) (fun t => (p t : ℂ))
      (fun t => aknsImagVector (g t)) x) =
      aknsPhysicalOperator (fun t => (q t : ℂ)) (fun t => (p t : ℂ))
        (fun t => aknsImagVector (g t)) x :=
  ⟨aknsPhysicalOperator_real q p (fun t => ((g t).1.re,(g t).2.re)) x,
    aknsPhysicalOperator_real q p (fun t => ((g t).1.im,(g t).2.im)) x⟩

end NLS.ZakharovShabat
