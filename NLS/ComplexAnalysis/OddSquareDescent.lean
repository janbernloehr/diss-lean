import NLS.ComplexAnalysis.ParametricDSlope
import NLS.ComplexAnalysis.LocalEvenSquareFamily
import NLS.ComplexAnalysis.EntireEvenSquareDescent

/-! The odd part of an entire scalar family, divided by its frequency,
descends jointly analytically through squaring, including zero energy.
The exact factor two is retained. -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- Filled quotient of the odd difference by twice the scalar frequency. -/
def oddPartQuotient (F : ℂ × A → ℂ) (p : ℂ × A) : ℂ :=
  jointDSlopeZero (fun t => F t-F (-t.1,t.2)) p/2

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem oddPartQuotient_eq_div (F : ℂ × A → ℂ) (a : A) (z : ℂ) (hz : z ≠ 0) :
    oddPartQuotient F (z,a) = (F (z,a)-F (-z,a))/(2*z) := by
  simp only [oddPartQuotient,jointDSlopeZero,dslope_of_ne _ hz,slope_def_field,
    neg_zero,sub_self,sub_zero]
  ring

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem oddPartQuotient_even (F : ℂ × A → ℂ) (a : A) (z : ℂ) :
    oddPartQuotient F (-z,a) = oddPartQuotient F (z,a) := by
  by_cases hz : z = 0
  · simp only [hz,neg_zero]
  · rw [oddPartQuotient_eq_div F a (-z) (neg_ne_zero.mpr hz),oddPartQuotient_eq_div F a z hz]
    simp only [neg_neg]
    ring

theorem analyticOnNhd_oddPartQuotient (F : ℂ × A → ℂ) (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (univ ×ˢ V)) :
    AnalyticOnNhd ℂ (oddPartQuotient F) (univ ×ˢ V) := by
  have hodd : AnalyticOnNhd ℂ (fun t : ℂ × A => F t-F (-t.1,t.2)) (univ ×ˢ V) := by
    intro p hp
    exact (hF p hp).sub ((hF (-p.1,p.2) ⟨mem_univ _,hp.2⟩).comp
      (f := fun t : ℂ × A => (-t.1,t.2)) (analyticAt_fst.neg.prod analyticAt_snd))
  intro p hp
  exact (analyticOnNhd_jointDSlopeZero _ V hV hodd p hp).div_const

/-- The energy numerator obtained by the filled odd quotient and square descent. -/
def oddSquareDescent (F : ℂ × A → ℂ) (p : ℂ × A) : ℂ :=
  oddPartQuotient F (Complex.sqrt p.1,p.2)

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem oddSquareDescent_sq (F : ℂ × A → ℂ) (a : A) (z : ℂ) :
    oddSquareDescent F (z^2,a) = oddPartQuotient F (z,a) := by
  rcases eq_or_eq_neg_of_sq_eq_sq (Complex.sqrt (z^2)) z (complex_sqrt_sq (z^2)) with h | h
  · simp only [oddSquareDescent,h]
  · simp only [oddSquareDescent,h,oddPartQuotient_even]

theorem analyticOnNhd_oddSquareDescent (F : ℂ × A → ℂ) (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (univ ×ˢ V)) :
    AnalyticOnNhd ℂ (oddSquareDescent F) (univ ×ˢ V) := by
  intro p hp
  let G : ℂ × (ℂ × A) → ℂ := fun t => oddPartQuotient F (t.1,t.2.2)
  have hq : AnalyticAt ℂ (fun t : ℂ × (ℂ × A) => t.2.2) (Complex.sqrt p.1,p) :=
    analyticAt_snd.comp (f := fun t : ℂ × (ℂ × A) => t.2) analyticAt_snd
  have hQ : AnalyticAt ℂ (oddPartQuotient F) (Complex.sqrt p.1,p.2) :=
    analyticOnNhd_oddPartQuotient F V hV hF _ ⟨mem_univ _,hp.2⟩
  have hG : AnalyticAt ℂ G (Complex.sqrt p.1,p) := by
    have h := hQ.comp (f := fun t : ℂ × (ℂ × A) => (t.1,t.2.2)) (analyticAt_fst.prod hq)
    simpa only [G,Function.comp_def] using h
  have he : ∀ b : ℂ × A, ∀ z : ℂ, G (-z,b) = G (z,b) := fun b z => oddPartQuotient_even F b.2 z
  have hs : AnalyticAt ℂ (fun b : ℂ × A => (Complex.sqrt b.1)^2) p := by
    simp only [complex_sqrt_sq]
    exact analyticAt_fst
  exact analyticAt_evenFamily_of_analytic_square G (fun b : ℂ × A => Complex.sqrt b.1) p hG he hs

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem oddSquareDescent_frequency_formula (F : ℂ × A → ℂ) (a : A) (z : ℂ) (hz : z ≠ 0) :
    oddSquareDescent F (z^2,a) = (F (z,a)-F (-z,a))/(2*z) := by
  rw [oddSquareDescent_sq,oddPartQuotient_eq_div F a z hz]

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- Exact differential pullback, also at zero frequency. -/
theorem two_mul_frequency_oddSquareDescent (F : ℂ × A → ℂ) (a : A) (z : ℂ) :
    2*z*oddSquareDescent F (z^2,a) = F (z,a)-F (-z,a) := by
  rw [oddSquareDescent_sq]
  have h := sub_smul_dslope (fun w : ℂ => F (w,a)-F (-w,a)) 0 z
  simp only [sub_zero,neg_zero,sub_self,smul_eq_mul] at h
  change 2*z*(dslope (fun w : ℂ => F (w,a)-F (-w,a)) 0 z/2) = _
  linear_combination h

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- The removable zero-energy value is the ORIGINAL frequency derivative. -/
theorem oddSquareDescent_zero (F : ℂ × A → ℂ) (a : A)
    (hf : AnalyticAt ℂ (fun z : ℂ => F (z,a)) 0) :
    oddSquareDescent F (0,a) = deriv (fun z : ℂ => F (z,a)) 0 := by
  have hd := hf.differentiableAt.hasDerivAt
  have hb : HasDerivAt (fun z : ℂ => F (z,a)) (deriv (fun z : ℂ => F (z,a)) 0) (-(0:ℂ)) := by
    simpa only [neg_zero] using hd
  have hn : HasDerivAt (fun z : ℂ => F (-z,a)) (-(deriv (fun z : ℂ => F (z,a)) 0)) 0 := by
    simpa only [Function.comp_def,mul_neg,mul_one] using hb.comp 0 ((hasDerivAt_id (0:ℂ)).neg)
  have ho := hd.sub hn
  have he : deriv (fun w : ℂ => F (w,a)-F (-w,a)) 0 =
      deriv (fun z : ℂ => F (z,a)) 0- -(deriv (fun z : ℂ => F (z,a)) 0) := ho.deriv
  simp only [oddSquareDescent,Complex.sqrt_zero,oddPartQuotient,jointDSlopeZero,dslope_same,he]
  ring

end NLS.ComplexAnalysis
