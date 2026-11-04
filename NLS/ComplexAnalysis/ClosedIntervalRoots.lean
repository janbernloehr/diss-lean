import NLS.ComplexAnalysis.SymmetricSegmentIncidence
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate ENNReal

namespace NLS.ComplexAnalysis

theorem isClosed_exists_zero_in_variable_Icc {T : Type*} [TopologicalSpace T]
    (F : T × ℝ → ℂ) (a b : T → ℝ) (hF : Continuous F) (ha : Continuous a) (hb : Continuous b)
    (hab : ∀ t, a t≤b t) : IsClosed {t : T | ∃ x∈Icc (a t) (b t), F (t,x)=0} := by
  let C : Set (T × Icc (0 : ℝ) 1) :=
    {p | F (p.1,(1-p.2.val)*a p.1+p.2.val*b p.1)=0}
  have hc : IsClosed C := by
    apply isClosed_eq _ continuous_const
    have ht : Continuous (fun p : T × Icc (0 : ℝ) 1 =>
        (p.1,(1-p.2.val)*a p.1+p.2.val*b p.1)) := by fun_prop
    exact hF.comp ht
  have hp := isClosedMap_fst_of_compactSpace C hc
  convert! hp using 1
  ext t
  constructor
  · rintro ⟨x,hx,hzero⟩
    have hseg : x∈segment ℝ (a t) (b t) := by
      simpa only [segment_eq_Icc (hab t)] using hx
    rw [segment_eq_image_lineMap] at hseg
    obtain ⟨s,hs,hxs⟩ := hseg
    refine ⟨(t,⟨s,hs⟩),?_,rfl⟩
    change F (t,(1-s)*a t+s*b t)=0
    have he : (1-s)*a t+s*b t=x := by
      simpa only [AffineMap.lineMap_apply_module,smul_eq_mul] using hxs
    rw [he]
    exact hzero
  · rintro ⟨⟨p,s⟩,hp,hpt⟩
    change p=t at hpt
    subst p
    refine ⟨(1-s.val)*a t+s.val*b t,?_,hp⟩
    constructor
    · nlinarith [s.property.1,s.property.2,hab t]
    · nlinarith [s.property.1,s.property.2,hab t]

end NLS.ComplexAnalysis
