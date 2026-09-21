import NLS.ZakharovShabat.CanonicalPeriodicGapOrder
import NLS.ZakharovShabat.PeriodicEndpointMultiplicity

/-!
# Critical points in every canonical real gap

The identified parity levels let Rolle apply to every open gap, including
the central gaps. Collapsed gaps are critical by original multiplicity.
This establishes existence in every gap; matching these critical points
to their canonical critical indices requires the central counting argument.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every open canonical real gap contains a critical point strictly between its endpoints. -/
theorem exists_critical_between_canonicalPeriodicEndpoints (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ)
    (hlt : (canonicalPeriodicLeft hp hp1 φ heven n).re < (canonicalPeriodicRight hp hp1 φ heven n).re) :
    ∃ c ∈ Ioo (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re,
      deriv (canonicalDiscriminant hp φ) (c : ℂ) = 0 := by
  obtain ⟨hi,hj⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ heven hreal n
  have hx : ((canonicalPeriodicLeft hp hp1 φ heven n).re : ℂ) = canonicalPeriodicLeft hp hp1 φ heven n := by
    apply Complex.ext <;> simp [hi]
  have hy : ((canonicalPeriodicRight hp hp1 φ heven n).re : ℂ) = canonicalPeriodicRight hp hp1 φ heven n := by
    apply Complex.ext <;> simp [hj]
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_discriminant_of_realType hp hp1 φ heven hreal n
  exact exists_discriminant_critical_between hp hp1 φ heven hreal hlt (by rw [hx,hy]; exact hl.trans hr.symm)

/-- A collapsed canonical pair is critical even at complex even potentials. -/
theorem canonicalPeriodicLeft_critical_of_eq_right (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (n : ℤ)
    (he : canonicalPeriodicLeft hp hp1 φ heven n = canonicalPeriodicRight hp hp1 φ heven n) :
    deriv (canonicalDiscriminant hp φ) (canonicalPeriodicLeft hp hp1 φ heven n) = 0 :=
  (canonicalPeriodicEndpoints_spec hp hp1 φ heven).1.critical_of_eq hp1 heven n he

/-- Every canonical closed real gap contains a critical point, whether open or collapsed. -/
theorem exists_critical_mem_canonicalPeriodicGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) :
    ∃ c ∈ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re,
      deriv (canonicalDiscriminant hp φ) (c : ℂ) = 0 := by
  have hle := re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.1 n)
  rcases lt_or_eq_of_le hle with hlt | he
  · obtain ⟨c,hc,hzero⟩ := exists_critical_between_canonicalPeriodicEndpoints hp hp1 φ heven hreal n hlt
    exact ⟨c,⟨hc.1.le,hc.2.le⟩,hzero⟩
  · obtain ⟨hi,hj⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ heven hreal n
    have hec : canonicalPeriodicLeft hp hp1 φ heven n = canonicalPeriodicRight hp hp1 φ heven n :=
      Complex.ext he (hi.trans hj.symm)
    have hx : ((canonicalPeriodicLeft hp hp1 φ heven n).re : ℂ) = canonicalPeriodicLeft hp hp1 φ heven n := by
      apply Complex.ext <;> simp [hi]
    refine ⟨(canonicalPeriodicLeft hp hp1 φ heven n).re,⟨le_rfl,he.le⟩,?_⟩
    rw [hx]
    exact canonicalPeriodicLeft_critical_of_eq_right hp hp1 φ heven n hec

end NLS.ZakharovShabat
