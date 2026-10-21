import NLS.ZakharovShabat.PeriodicSpectrum

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A constant potential in the actual period-two operator space. -/
def constantPeriodicPair (a b : ℂ) : PairSpace p :=
  (lp.single p 0 a, lp.single p 0 b)

@[simp] theorem operator_constantPeriodicPair_fst (hp : p ≠ ⊤) (a b : ℂ)
    (f : Domain p) (k : ℤ) :
    (operator hp (constantPeriodicPair a b) f).1 k =
      -(Real.pi : ℂ) * k * f.1.val k + a * f.2.val k := by
  rw [operator_fst_apply]
  simp [constantPeriodicPair, lp.single_apply, Pi.single_apply, ite_mul, sub_eq_zero]

@[simp] theorem operator_constantPeriodicPair_snd (hp : p ≠ ⊤) (a b : ℂ)
    (f : Domain p) (k : ℤ) :
    (operator hp (constantPeriodicPair a b) f).2 k =
      (Real.pi : ℂ) * k * f.2.val k + b * f.1.val k := by
  rw [operator_snd_apply]
  simp [constantPeriodicPair, lp.single_apply, Pi.single_apply, ite_mul, sub_eq_zero]

/-- Every nonzero eigenvector has a nonzero first coefficient when a is nonzero. -/
theorem constantPeriodicPair_eigenvector_has_fst (hp : p ≠ ⊤) (a b z : ℂ)
    (ha : a ≠ 0) (f : Domain p) (hf : f ≠ 0)
    (he : operator hp (constantPeriodicPair a b) f = z • domainInclusion f) :
    ∃ k : ℤ, f.1.val k ≠ 0 := by
  by_contra h
  push Not at h
  have hs (k : ℤ) : f.2.val k = 0 := by
    have hk := congrArg (fun u : PairSpace p => u.1 k) he
    simp only [operator_constantPeriodicPair_fst, Prod.smul_fst, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, domainInclusion_apply, scalarInclusion_apply] at hk
    change -(Real.pi : ℂ) * k * f.1.val k + a * f.2.val k = z * f.1.val k at hk
    rw [h k, mul_zero, zero_add, mul_zero] at hk
    exact (mul_eq_zero.mp hk).resolve_left ha
  apply hf
  apply Prod.ext <;> apply Subtype.ext <;> funext k
  · exact h k
  · exact hs k

/-- The exact characteristic equation of a constant-potential eigenvalue. -/
theorem constantPeriodicPair_eigenvalue_equation (hp : p ≠ ⊤) (a b z : ℂ)
    (ha : a ≠ 0) (hz : z ∈ periodicSpectrum hp (constantPeriodicPair a b)) :
    ∃ k : ℤ, z^2 = ((Real.pi : ℂ) * k)^2 + a*b := by
  obtain ⟨f,hf,he⟩ := (mem_periodicSpectrum_iff_exists_eigenvector hp _ z).mp hz
  obtain ⟨k,hk⟩ := constantPeriodicPair_eigenvector_has_fst hp a b z ha f hf he
  refine ⟨k,?_⟩
  have h₁ := congrArg (fun u : PairSpace p => u.1 k) he
  have h₂ := congrArg (fun u : PairSpace p => u.2 k) he
  simp only [operator_constantPeriodicPair_fst, Prod.smul_fst, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, domainInclusion_apply, scalarInclusion_apply] at h₁
  simp only [operator_constantPeriodicPair_snd, Prod.smul_snd, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, domainInclusion_apply, scalarInclusion_apply] at h₂
  change -(Real.pi : ℂ) * k * f.1.val k + a * f.2.val k = z * f.1.val k at h₁
  change (Real.pi : ℂ) * k * f.2.val k + b * f.1.val k = z * f.2.val k at h₂
  have hm : (z^2 - (((Real.pi : ℂ) * k)^2 + a*b)) * f.1.val k = 0 := by
    linear_combination -(z - (Real.pi : ℂ)*k) * h₁ - a * h₂
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hk)

/-- An explicit single-mode eigenvector proves the converse equation. -/
theorem mem_periodicSpectrum_constantPeriodicPair_of_equation (hp : p ≠ ⊤)
    (a b z : ℂ) (ha : a ≠ 0) (k : ℤ)
    (hz : z^2 = ((Real.pi : ℂ)*k)^2 + a*b) :
    z ∈ periodicSpectrum hp (constantPeriodicPair a b) := by
  let f : Domain p := (scalarMode k a, scalarMode k (z+(Real.pi : ℂ)*k))
  apply (mem_periodicSpectrum_iff_exists_eigenvector hp _ z).mpr
  refine ⟨f,?_,?_⟩
  · intro hf
    have hk := congrArg (fun u : Domain p => u.1.val k) hf
    simp [f, ha] at hk
  · apply Prod.ext <;> ext j
    · simp only [Prod.smul_fst, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        domainInclusion_apply, scalarInclusion_apply]
      change (operator hp (constantPeriodicPair a b) f).1 j = z * f.1.val j
      rw [operator_constantPeriodicPair_fst]
      by_cases hj : j = k
      · subst j; simp only [f, scalarMode_apply, ite_true]; ring
      · simp [f, scalarMode_apply, hj]
    · simp only [Prod.smul_snd, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        domainInclusion_apply, scalarInclusion_apply]
      change (operator hp (constantPeriodicPair a b) f).2 j = z * f.2.val j
      rw [operator_constantPeriodicPair_snd]
      by_cases hj : j = k
      · subst j
        simp only [f, scalarMode_apply, ite_true]
        linear_combination -hz
      · simp [f, scalarMode_apply, hj]

/-- Exact membership in the actual periodic spectrum for constant complex potentials. -/
theorem mem_periodicSpectrum_constantPeriodicPair_iff (hp : p ≠ ⊤)
    (a b z : ℂ) (ha : a ≠ 0) :
    z ∈ periodicSpectrum hp (constantPeriodicPair a b) ↔
      ∃ k : ℤ, z^2 = ((Real.pi : ℂ)*k)^2 + a*b := by
  constructor
  · exact constantPeriodicPair_eigenvalue_equation hp a b z ha
  · rintro ⟨k,hk⟩
    exact mem_periodicSpectrum_constantPeriodicPair_of_equation hp a b z ha k hk

end NLS.ZakharovShabat
