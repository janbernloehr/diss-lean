import NLS.FunctionalAnalysis.RealSheetEndpoint
import Mathlib.Analysis.Complex.Basic

/-! Reachability for complete bounded complex spectral-sheet trajectories.
The supplied equations are actual two-coordinate ODEs; no hitting time
or finite-gap hypothesis is supplied. -/
noncomputable section
open Set Complex
namespace NLS.FunctionalAnalysis

theorem exists_endpoint_of_bounded_complex_sheetODE
    (μ S : ℝ → ℂ) (Δ : ℂ → ℂ) (a b : ℝ)
    (hμim : ∀ t : ℝ, (μ t).im=0) (hSim : ∀ t : ℝ, (S t).im=0)
    (hder : ∀ t : ℝ, HasDerivAt μ (S t/2) t ∧ HasDerivAt S (Δ (μ t)*deriv Δ (μ t)/2) t)
    (hx : ∀ t : ℝ, (μ t).re ∈ Icc a b)
    (hcomplexSheet : ∀ t : ℝ, (S t)^2=(Δ (μ t))^2-4)
    (hΔreal : ∀ y : ℝ, (Δ (y:ℂ)).im=0)
    (hΔderreal : ∀ y : ℝ, (deriv Δ (y:ℂ)).im=0)
    (hΔC : Continuous Δ) (hΔ'C : Continuous (deriv Δ))
    (hEnds : (Δ (a:ℂ))^2-4=0 ∧ (Δ (b:ℂ))^2-4=0)
    (hEndpointOnly : ∀ y ∈ Icc a b, (Δ (y:ℂ))^2-4=0 → y=a ∨ y=b)
    (hSimple : a < b → Δ (a:ℂ)*deriv Δ (a:ℂ) ≠ 0 ∧ Δ (b:ℂ)*deriv Δ (b:ℂ) ≠ 0) :
    ∃ t : ℝ, S t=0 ∧ (μ t=(a:ℂ) ∨ μ t=(b:ℂ)) := by
  let x : ℝ → ℝ := fun t => (μ t).re
  let v : ℝ → ℝ := fun t => (S t).re/2
  let F : ℝ → ℝ := fun y => (Δ (y:ℂ)*deriv Δ (y:ℂ)).re/4
  let G : ℝ → ℝ := fun y => ((Δ (y:ℂ)).re^2-4)/4
  have hμcast (t : ℝ) : (x t : ℂ)=μ t := Complex.ext rfl (by simpa only [ofReal_im] using (hμim t).symm)
  have hxder (t : ℝ) : HasDerivAt x (v t) t := by
    simpa only [Function.comp_def,Complex.reCLM_apply,div_ofNat_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hder t).1
  have hvder (t : ℝ) : HasDerivAt v (F (x t)) t := by
    have hd := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hder t).2).div_const 2
    apply hd.congr_deriv
    change (Δ (μ t)*deriv Δ (μ t)/2).re/2=F (x t)
    dsimp only [F]
    rw [hμcast t]
    simp only [div_ofNat_re]
    ring
  have hsheet (t : ℝ) : (v t)^2=G (x t) := by
    have hs : (S t)^2=(Δ (μ t))^2-4 := hcomplexSheet t
    rw [← hμcast t] at hs
    have hr := congrArg Complex.re hs
    simp only [pow_two,mul_re,sub_re,hSim t,hΔreal (x t),mul_zero,sub_zero,
      show (4:ℂ).re=4 from rfl] at hr
    dsimp only [v,G]
    nlinarith
  have hGend (y : ℝ) (hy : y ∈ Icc a b) (hy0 : G y=0) : y=a ∨ y=b := by
    have hz : (Δ (y:ℂ))^2-4=0 := by
      apply Complex.ext
      · change ((Δ (y:ℂ))^2-4).re=0
        simp only [pow_two,mul_re,sub_re,hΔreal y,mul_zero,sub_zero,
          show (4:ℂ).re=4 from rfl]
        change ((Δ (y:ℂ)).re^2-4)/4=0 at hy0
        nlinarith
      · change ((Δ (y:ℂ))^2-4).im=0
        simp only [pow_two,mul_im,sub_im,hΔreal y,mul_zero,zero_mul,add_zero,
          show (4:ℂ).im=0 from rfl,sub_zero]
    exact hEndpointOnly y hy hz
  have hSzero : ∃ t : ℝ, S t=0 := by
    have hab : a ≤ b := (hx 0).1.trans (hx 0).2
    rcases lt_or_eq_of_le hab with hopen | hcollapse
    · have hsimple := hSimple hopen
      have hF : Continuous F :=
        (continuous_re.comp ((hΔC.comp continuous_ofReal).mul (hΔ'C.comp continuous_ofReal))).div_const 4
      have hG : Continuous G :=
        ((continuous_re.comp (hΔC.comp continuous_ofReal)).pow 2 |>.sub continuous_const).div_const 4
      have hzeros (y : ℝ) (hy : y ∈ Icc a b) (hy0 : G y=0) : F y ≠ 0 := by
        have hp : Δ (y:ℂ)*deriv Δ (y:ℂ) ≠ 0 := by
          rcases hGend y hy hy0 with rfl | rfl
          · exact hsimple.1
          · exact hsimple.2
        have hre : (Δ (y:ℂ)*deriv Δ (y:ℂ)).re ≠ 0 := by
          intro he
          apply hp
          apply Complex.ext he
          simp only [mul_im,hΔreal y,hΔderreal y,mul_zero,zero_mul,add_zero,zero_im]
        exact div_ne_zero hre (by norm_num)
      obtain ⟨t,ht⟩ := exists_zero_velocity_of_bounded_sheetODE x v F G a b hxder hvder hx hsheet hF hG hzeros
      refine ⟨t,Complex.ext ?_ (hSim t)⟩
      change (S t).re/2=0 at ht
      change (S t).re=0
      linarith
    · have hxa : x 0=a := le_antisymm (by simpa only [hcollapse] using (hx 0).2) (hx 0).1
      have hμa : μ 0=(a:ℂ) := by rw [← hμcast 0,hxa]
      have hz : (Δ (μ 0))^2-4=0 := by rw [hμa]; exact hEnds.1
      have hs : (S 0)^2=0 := (hcomplexSheet 0).trans hz
      exact ⟨0,sq_eq_zero_iff.mp hs⟩
  obtain ⟨t,ht⟩ := hSzero
  have hG0 : G (x t)=0 := by rw [← hsheet t]; simp only [v,ht,zero_re,zero_div,zero_pow (by decide : (2:ℕ) ≠ 0)]
  refine ⟨t,ht,?_⟩
  rcases hGend (x t) (hx t) hG0 with he | he
  · exact Or.inl (Complex.ext he (by simpa only [ofReal_im] using hμim t))
  · exact Or.inr (Complex.ext he (by simpa only [ofReal_im] using hμim t))

end NLS.FunctionalAnalysis
