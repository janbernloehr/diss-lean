import NLS.ZakharovShabat.ClassicalSignedSpectrum

/-! # Physical differential-equation eigenvalues equal the actual classical signed spectrum -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The original differential equation on a nonzero full classical signed H¹ input. -/
def classicalSignedEigenvalues (u : IntervalPairL2) (r : ℤ) : Set ℂ :=
  {z | ∃ (f : ℝ → ℂ × ℂ) (hf : HasClassicalParityDomain r f),
    intervalL2OfFunction f hf.memLp ≠ 0 ∧
      physicalOperator (intervalL2Representative u) f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)}

/-- Acting on the included classical function yields its eigenvalue multiple exactly when the original ODE holds. -/
theorem classicalSignedOperator_classical_eigenvalue_iff (u : IntervalPairL2) (r : ℤ) (z : ℂ)
    (f : ℝ → ℂ × ℂ) (hf : HasClassicalParityDomain r f) :
    classicalSignedOperator u r (unitParityDomainEquiv r (sourceClassicalParityExtension r f hf)) =
      z • intervalL2OfFunction f hf.memLp ↔
    physicalOperator (intervalL2Representative u) f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x) := by
  have hrep := classicalSignedOperator_representative u r f hf
  have hs := intervalL2Representative_smul z (intervalL2OfFunction f hf.memLp)
  have hf' := intervalL2Representative_ofFunction f hf.memLp
  constructor
  · intro he
    rw [he] at hrep
    filter_upwards [hrep,hs,hf'] with x hx hy hz
    rw [← hx,hy,hz]
  · intro he
    apply intervalL2Representative_injective
    filter_upwards [hrep,hs,hf',he] with x hx hy hz hw
    rw [hx,hw,hy,hz]

/-- No continuous or residual spectrum remains: the actual bounded-inverse complement is exactly the original ODE eigenvalue set. -/
theorem classicalSignedSpectrum_eq_eigenvalues (u : IntervalPairL2) (r : ℤ) :
    classicalSignedSpectrum u r = classicalSignedEigenvalues u r := by
  ext z
  rw [mem_classicalSignedSpectrum_iff_exists_kernel]
  constructor
  · rintro ⟨a,hne,ha⟩
    obtain ⟨f,hf,hclass⟩ := (classicalSignedOperator_domain_iff u a.val r).mp a.property
    let g : (classicalSignedOperator u r).domain :=
      unitParityDomainEquiv r (sourceClassicalParityExtension r f hf)
    have hg : g = a := by
      apply Subtype.ext
      change unitParityDomainInclusion r (sourceClassicalParityExtension r f hf) = a.val
      rw [unitParityDomainInclusion_classicalExtension,hclass]
    have he : classicalSignedOperator u r g = z • intervalL2OfFunction f hf.memLp := by
      rw [hg,hclass]
      exact (sub_eq_zero.mp ha).symm
    exact ⟨f,hf,by simpa only [hclass] using hne,
      (classicalSignedOperator_classical_eigenvalue_iff u r z f hf).mp he⟩
  · rintro ⟨f,hf,hne,hode⟩
    let g : (classicalSignedOperator u r).domain :=
      unitParityDomainEquiv r (sourceClassicalParityExtension r f hf)
    have hval : (g : IntervalPairL2) = intervalL2OfFunction f hf.memLp :=
      unitParityDomainInclusion_classicalExtension r f hf
    have he := (classicalSignedOperator_classical_eigenvalue_iff u r z f hf).mpr hode
    refine ⟨g,by simpa only [hval] using hne,?_⟩
    rw [linearPMapPencil_apply,hval]
    change z • intervalL2OfFunction f hf.memLp -
      classicalSignedOperator u r (unitParityDomainEquiv r (sourceClassicalParityExtension r f hf)) = 0
    rw [he,sub_self]

/-- The printed combined periodic spectrum is exactly the union of the two full classical ODE eigenvalue sets. -/
theorem classicalSignedEigenvalues_union_eq_periodic (u : IntervalPairL2) :
    classicalSignedEigenvalues u 0 ∪ classicalSignedEigenvalues u 1 =
      periodicSpectrum (by simp) (periodOnePotential (sourcePhysicalL2Equiv.symm u)) := by
  rw [← classicalSignedSpectrum_eq_eigenvalues,← classicalSignedSpectrum_eq_eigenvalues,
    classicalSignedSpectrum_union_eq_periodic]

end NLS.ZakharovShabat
