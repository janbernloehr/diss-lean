import NLS.ComplexAnalysis.ParametricDSlope
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! A removable divided difference with an analytic moving center is
jointly Banach analytic, including on the whole diagonal. -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem dslope_translate_center (f : ℂ → ℂ) (a z : ℂ) :
    dslope (fun w => f (w+a)) 0 (z-a)=dslope f a z := by
  by_cases hz : z=a
  · subst z
    rw [sub_self,dslope_same,dslope_same,deriv_comp_add_const,zero_add]
  · simp only [dslope_of_ne _ (sub_ne_zero.mpr hz),dslope_of_ne _ hz,
      slope_def_field,sub_add_cancel,zero_add,sub_zero]

theorem analyticOnNhd_dslope_at_analytic_center
    (F : ℂ × A → ℂ) (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (univ ×ˢ V)) (s : A → ℂ) (hs : AnalyticOnNhd ℂ s V) :
    AnalyticOnNhd ℂ (fun t : ℂ × A => dslope (fun w => F (w,t.2)) (s t.2) t.1) (univ ×ˢ V) := by
  let G : ℂ × A → ℂ := fun t => F (t.1+s t.2,t.2)
  have hG : AnalyticOnNhd ℂ G (univ ×ˢ V) := by
    intro t ht
    have hS := (hs t.2 ht.2).comp (f := fun p : ℂ × A => p.2) analyticAt_snd
    exact (hF (t.1+s t.2,t.2) ⟨mem_univ _,ht.2⟩).comp
      (f := fun p : ℂ × A => (p.1+s p.2,p.2)) ((analyticAt_fst.add hS).prod analyticAt_snd)
  have hQ := analyticOnNhd_jointDSlopeZero G V hV hG
  intro t ht
  have hS := (hs t.2 ht.2).comp (f := fun p : ℂ × A => p.2) analyticAt_snd
  have ha := (hQ (t.1-s t.2,t.2) ⟨mem_univ _,ht.2⟩).comp
    (f := fun p : ℂ × A => (p.1-s p.2,p.2)) ((analyticAt_fst.sub hS).prod analyticAt_snd)
  convert ha using 1
  funext p
  exact (dslope_translate_center (fun w => F (w,p.2)) (s p.2) p.1).symm

end NLS.ComplexAnalysis
