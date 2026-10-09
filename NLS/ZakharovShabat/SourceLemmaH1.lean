import NLS.ZakharovShabat.SobolevRiccatiWeakHierarchy
import NLS.ZakharovShabat.SobolevSourceSmoothDensity
import NLS.ZakharovShabat.SobolevDifferentialPolynomial
import NLS.ZakharovShabat.NLSRiccatiPolynomialRemainder

/-! # H.1 at the printed H^(k-1) regularity

Write k=s+1. The independently constructed weak Riccati density equals
-b^(k) plus the canonical lower-jet polynomial. The identity is proved
at every Fourier coefficient by continuity from smooth complex sources.
-/
noncomputable section
open Set NLS.Fourier NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The actual Fourier coefficient of the continuous lower-jet remainder field. -/
def sourceH1RemainderCoefficient (s : ℕ) (ab : SobolevSource s) (j : ℤ) : ℂ :=
  continuousFourierCLM (sobolevPolynomialField s (nlsRiccatiRemainder (s+1)) ab) (2*j)

/-- The ambient even coefficient is exactly the original period-one Fourier integral. -/
theorem sourceH1RemainderCoefficient_eq_integral (s : ℕ) (ab : SobolevSource s) (j : ℤ) :
    sourceH1RemainderCoefficient s ab j = periodOneCoefficient
      (fun x : ℝ => sobolevPolynomialField s (nlsRiccatiRemainder (s+1)) ab (x : AddCircle (2 : ℝ))) j := by
  rw [sourceH1RemainderCoefficient,continuousFourierCLM_apply,← periodTwoCoefficient_circle]
  exact periodTwoCoefficient_periodic_even _ (sobolevPolynomialField_periodic _ _ _)
    (((sobolevPolynomialField s (nlsRiccatiRemainder (s+1)) ab).continuous.comp
      continuous_quotient_mk').intervalIntegrable 0 1) j

/-- Every lower-jet remainder coefficient depends analytically on the full Hˢ source. -/
theorem analyticAt_sourceH1RemainderCoefficient (s : ℕ) (ab : SobolevSource s) (j : ℤ) :
    AnalyticAt ℂ (fun cd => sourceH1RemainderCoefficient s cd j) ab :=
  ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (2*j)).analyticAt _).comp
    ((continuousFourierCLM.analyticAt _).comp (analyticAt_sobolevPolynomialField s _ ab))

/-- The printed jet-order bound puts every nonlinear jet strictly below the source regularity. -/
theorem sourceH1_remainder_jetOrder (s : ℕ) (hs : 1 ≤ s) :
    JetOrderLE (nlsRiccatiRemainder (s+1)) (s-1) := by
  apply JetOrderLE.of_derivativeOrder (nlsRiccatiRemainder_derivativeOrder (s+1))
  omega

/-- Smooth comparison uses only the genuinely available lower jets; the H⁰ remainder is zero. -/
theorem sourceH1RemainderCoefficient_eq_classical
    (s : ℕ) (ab : SobolevSource s) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (ha : ∀ j, ab.1.val j = periodOneCoefficient f j)
    (hb : ∀ j, ab.2.val j = periodOneCoefficient g j) (j : ℤ) :
    sourceH1RemainderCoefficient s ab j = periodOneCoefficient
      (evaluate f g (nlsRiccatiRemainder (s+1))) j := by
  rw [sourceH1RemainderCoefficient_eq_integral]
  congr 1
  funext x
  by_cases hs : 1 ≤ s
  · exact sobolevPolynomialField_eq_classical s hs _ (sourceH1_remainder_jetOrder s hs)
      ab f g hf hg hpf hpg ha hb x
  · have hs0 : s = 0 := by omega
    subst s
    simp [nlsRiccatiRemainder_one,sobolevPolynomialField,evaluate]

/-- H.1's leading derivative and nonlinear remainder at every original Fourier mode,
on all complex H^(k-1) sources, with k=s+1. -/
theorem sourceLemmaH1 (s : ℕ) (ab : SobolevSource s) (j : ℤ) :
    (weakSobolevRiccatiDensity s ab).val j =
      -(2*Complex.I*(Real.pi : ℂ)*j)^(s+1)*ab.2.val j+sourceH1RemainderCoefficient s ab j := by
  let F := fun cd : SobolevSource s => (weakSobolevRiccatiDensity s cd).val j
  let G := fun cd : SobolevSource s =>
    -(2*Complex.I*(Real.pi : ℂ)*j)^(s+1)*cd.2.val j+sourceH1RemainderCoefficient s cd j
  have hF : Continuous F := (WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 j).continuous.comp
    (continuous_iff_continuousAt.mpr (fun cd => (analyticAt_weakSobolevRiccatiDensity s cd).continuousAt))
  have hG : Continuous G :=
    (continuous_const.mul ((WeightedCoeff.evalCLM (Weight.sobolev (s : ℝ)) 2 j).continuous.comp
      continuous_snd)).add
      (continuous_iff_continuousAt.mpr (fun cd => (analyticAt_sourceH1RemainderCoefficient s cd j).continuousAt))
  have he : F = G := eq_of_continuous_of_smooth_sobolevSource s F G hF hG (by
    intro cd f g hf hg hpf hpg ha hb
    dsimp only [F,G]
    rw [weakSobolevRiccatiDensity_eq_classical_coefficients s cd f g hf hg hpf hpg ha hb,
      sourceH1RemainderCoefficient_eq_classical s cd f g hf hg hpf hpg ha hb,
      nlsRiccatiDensity_eq_leading_add_remainder f g hf hg,
      periodOneCoefficient_add (-iteratedDeriv (s+1) g) (evaluate f g (nlsRiccatiRemainder (s+1)))
        (contDiff_iteratedDeriv_of_smooth g hg (s+1)).neg.continuous
        (continuous_evaluate f g hf hg _),periodOneCoefficient_neg,
      periodOneCoefficient_iteratedDeriv_of_smooth g hg hpg,hb]
    ring)
  exact congrFun he ab

/-- The canonical polynomial has every grading and derivative-count property in H.1,
independently of the source at which it is evaluated. -/
theorem sourceLemmaH1_polynomial (s : ℕ) :
    (nlsRiccatiRemainder (s+1)).IsWeightedHomogeneous totalWeight (s+2) ∧
    (MvPolynomial.X (false,0)*nlsRiccatiRemainder (s+1)).IsWeightedHomogeneous fieldCharge 0 ∧
    DerivativeOrderLE (MvPolynomial.X (false,0)*nlsRiccatiRemainder (s+1)) ((s : ℤ)-1) ∧
    ∀ v ∈ (nlsRiccatiRemainder (s+1)).vars, (v.2 : ℤ) ≤ (s : ℤ)-1 := by
  obtain ⟨_,hc,hd⟩ := nlsRiccatiRemainder_hamiltonian_grades (s+1)
  refine ⟨?_,hc,?_,?_⟩
  · convert nlsRiccatiRemainder_totalWeight (s+1) using 1
    push_cast
    ring
  · convert hd using 1; push_cast; ring
  · intro v hv
    have h := nlsRiccatiRemainder_vars (s+1) v hv
    push_cast at h
    omega

/-- The weak recurrence is the unique continuous H⁻¹ extension of the actual smooth hierarchy. -/
theorem weakSobolevRiccatiDensity_unique (s : ℕ) (F : SobolevSource s → WeakRiccatiSpace)
    (hF : Continuous F)
    (hclassical : ∀ (ab : SobolevSource s) (f g : ℝ → ℂ),
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → Function.Periodic f 1 → Function.Periodic g 1 →
      (∀ j, ab.1.val j = periodOneCoefficient f j) →
      (∀ j, ab.2.val j = periodOneCoefficient g j) →
      ∀ j, (F ab).val j = periodOneCoefficient (nlsRiccatiDensity f g (s+1)) j) :
    F = weakSobolevRiccatiDensity s := by
  apply eq_of_continuous_of_smooth_sobolevSource s F _ hF
    (continuous_iff_continuousAt.mpr (fun cd => (analyticAt_weakSobolevRiccatiDensity s cd).continuousAt))
  intro ab f g hf hg hpf hpg ha hb
  apply Subtype.ext
  funext j
  exact (hclassical ab f g hf hg hpf hpg ha hb j).trans
    (weakSobolevRiccatiDensity_eq_classical_coefficients s ab f g hf hg hpf hpg ha hb j).symm

end NLS.ZakharovShabat
