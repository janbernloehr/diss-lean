import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Basic

/-! Period-one unitary characters are locally constant in any jointly
continuous family, by averaging over one physical period. No winding
classification or local compactness of the parameter space is assumed. -/
noncomputable section
open Set Complex Filter Topology MeasureTheory
namespace NLS.ComplexAnalysis

/-- A period-one character with nonzero period average is trivial. -/
theorem periodic_character_eq_one_of_integral_ne_zero (h : ℝ → ℂ)
    (ha : ∀ s t, h (s+t)=h s*h t) (hp : Function.Periodic h 1)
    (hA : (∫ t in (0:ℝ)..1, h t) ≠ 0) (s : ℝ) : h s=1 := by
  have he : h s*(∫ t in (0:ℝ)..1, h t)=∫ t in (0:ℝ)..1, h t := by
    rw [← intervalIntegral.integral_const_mul]
    simp_rw [← ha]
    rw [intervalIntegral.integral_comp_add_left]
    simpa only [add_zero,zero_add] using hp.intervalIntegral_add_eq s 0
  have hz : (h s-1)*(∫ t in (0:ℝ)..1, h t)=0 := by
    rw [sub_mul,he,one_mul,sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hA)

/-- Nonzero averaged correlation identifies two unitary period-one characters. -/
theorem periodic_characters_eq_of_correlation_ne_zero (f g : ℝ → ℂ)
    (hf : ∀ s t, f (s+t)=f s*f t) (hg : ∀ s t, g (s+t)=g s*g t)
    (hfp : Function.Periodic f 1) (hgp : Function.Periodic g 1)
    (hgn : ∀ t, ‖g t‖=1)
    (hA : (∫ t in (0:ℝ)..1, f t*(starRingEnd ℂ) (g t)) ≠ 0) : f=g := by
  have hunit (t : ℝ) : g t*(starRingEnd ℂ) (g t)=1 := by
    rw [mul_conj,normSq_eq_norm_sq,hgn]
    norm_num
  funext s
  have he := periodic_character_eq_one_of_integral_ne_zero
    (fun t => f t*(starRingEnd ℂ) (g t))
    (fun a b => by rw [hf,hg,map_mul]; ring)
    (fun t => by change f (t+1)*(starRingEnd ℂ) (g (t+1))=f t*(starRingEnd ℂ) (g t); rw [hfp t,hgp t]) hA s
  have hm := congrArg (fun z : ℂ => z*g s) he
  have hcunit : (starRingEnd ℂ) (g s)*g s=1 := by rw [mul_comm]; exact hunit s
  simpa only [mul_assoc,hcunit,mul_one,one_mul] using hm

/-- A jointly continuous family of unitary period-one characters is locally
constant in its parameter, uniformly for ALL real displacements. -/
theorem exists_open_eq_periodic_character_family
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (F : X → ℝ → ℂ) (hc : Continuous F.uncurry)
    (ha : ∀ x s t, F x (s+t)=F x s*F x t)
    (hp : ∀ x, Function.Periodic (F x) 1) (hn : ∀ x t, ‖F x t‖=1) (a : X) :
    ∃ U : Set X, IsOpen U ∧ a ∈ U ∧ ∀ x ∈ U, F x=F a := by
  let G : X → ℝ → ℂ := fun x t => F x t*(starRingEnd ℂ) (F a t)
  have hcG : Continuous G.uncurry := by
    exact hc.mul (Complex.continuous_conj.comp
      ((hc.comp (continuous_const.prodMk continuous_id)).comp continuous_snd))
  have hGnorm (x : X) (t : ℝ) : ‖G x t‖=1 := by
    dsimp only [G]
    rw [norm_mul,Complex.norm_conj,hn,hn,one_mul]
  have hcont : Continuous (fun x => ∫ t in (0:ℝ)..1, G x t) := by
    apply intervalIntegral.continuous_of_dominated_interval (bound:=fun _ => (1:ℝ))
    · intro x
      exact (hcG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro x
      exact Eventually.of_forall (fun t _ => (hGnorm x t).le)
    · exact intervalIntegrable_const
    · exact Eventually.of_forall (fun t _ => hcG.comp (continuous_id.prodMk continuous_const))
  have hGa : (∫ t in (0:ℝ)..1, G a t)=1 := by
    have he : G a=(fun _ => (1:ℂ)) := by
      funext t
      dsimp only [G]
      rw [mul_conj,normSq_eq_norm_sq,hn]
      norm_num
    rw [he]
    norm_num
  let U := {x | (∫ t in (0:ℝ)..1, G x t) ≠ 0}
  refine ⟨U,isClosed_singleton.isOpen_compl.preimage hcont,?_,?_⟩
  · change (∫ t in (0:ℝ)..1, G a t) ≠ 0
    rw [hGa]
    exact one_ne_zero
  · intro x hx
    exact periodic_characters_eq_of_correlation_ne_zero (F x) (F a) (ha x) (ha a)
      (hp x) (hp a) (hn a) hx

end NLS.ComplexAnalysis
