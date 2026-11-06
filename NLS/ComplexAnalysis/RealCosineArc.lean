import NLS.ComplexAnalysis.PrimitiveRadialContinuation
import NLS.ComplexAnalysis.CosineSegmentGeometry

noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis

def realCosineArcAnchor (θ : ℝ) : ℝ := if θ<0 then -Real.pi else Real.pi

/-- A regular signed real terminal angle has a connected real angle
arc containing its terminal and the interior of its actual straight path
from the appropriate left-energy endpoint, with no sine zeros. -/
theorem exists_regular_real_cosine_arc (θ : ℝ)
    (hθ : θ∈Ioo (-Real.pi) Real.pi) (hn : θ≠0) :
    ∃ S : Set ℂ, IsPreconnected S ∧ (θ:ℂ)∈S ∧
      (∀ z∈S, z.im=0) ∧ (∀ z∈S, Complex.sin z≠0) ∧
      ∀ t∈Ioo (0:ℝ) 1,
        (Path.segment (realCosineArcAnchor θ:ℂ) (θ:ℂ)).extend t∈S := by
  by_cases hneg : θ<0
  · let S : Set ℂ := Complex.ofReal '' Ioo (-Real.pi) (0:ℝ)
    refine ⟨S,isPreconnected_Ioo.image _ continuous_ofReal.continuousOn,⟨θ,⟨hθ.1,hneg⟩,rfl⟩,
      ?_,?_,?_⟩
    · rintro z ⟨x,hx,rfl⟩
      exact ofReal_im _
    · rintro z ⟨x,hx,rfl⟩
      have hs := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hx.2) (by linarith [hx.1] : -x<Real.pi)
      rw [Real.sin_neg] at hs
      rw [← Complex.ofReal_sin]
      exact ofReal_ne_zero.mpr (ne_of_lt (by linarith : Real.sin x<0))
    · intro t ht
      rw [Path.extend_apply _ (Ioo_subset_Icc_self ht)]
      change AffineMap.lineMap (realCosineArcAnchor θ:ℂ) (θ:ℂ) t∈S
      have hp : 0<θ+Real.pi := by linarith [hθ.1]
      refine ⟨-Real.pi+t*(θ+Real.pi),⟨?_,?_⟩,?_⟩
      · nlinarith [mul_pos ht.1 hp]
      · have hm := mul_lt_mul_of_pos_right ht.2 hp
        nlinarith
      · rw [AffineMap.lineMap_apply_module']
        simp only [realCosineArcAnchor,if_pos hneg,Complex.real_smul]
        push_cast
        ring
  · have hpos : 0<θ := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hn)
    let S : Set ℂ := Complex.ofReal '' Ioo (0:ℝ) Real.pi
    refine ⟨S,isPreconnected_Ioo.image _ continuous_ofReal.continuousOn,⟨θ,⟨hpos,hθ.2⟩,rfl⟩,
      ?_,?_,?_⟩
    · rintro z ⟨x,hx,rfl⟩
      exact ofReal_im _
    · rintro z ⟨x,hx,rfl⟩
      rw [← Complex.ofReal_sin]
      exact ofReal_ne_zero.mpr (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2))
    · intro t ht
      rw [Path.extend_apply _ (Ioo_subset_Icc_self ht)]
      change AffineMap.lineMap (realCosineArcAnchor θ:ℂ) (θ:ℂ) t∈S
      have hp : 0<Real.pi-θ := by linarith [hθ.2]
      refine ⟨Real.pi+t*(θ-Real.pi),⟨?_,?_⟩,?_⟩
      · have hm := mul_lt_mul_of_pos_right ht.2 hp
        nlinarith
      · nlinarith [mul_pos ht.1 hp]
      · rw [AffineMap.lineMap_apply_module']
        simp only [realCosineArcAnchor,if_neg hneg,Complex.real_smul]
        push_cast
        ring

end NLS.ComplexAnalysis
