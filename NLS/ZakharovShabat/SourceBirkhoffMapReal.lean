import NLS.ZakharovShabat.SourceBirkhoffMapAnalytic
import NLS.ZakharovShabat.SourceBirkhoffCoordinateAngle
import NLS.ZakharovShabat.SourceAngularRealCharts

/-! # Reality of the actual rectangular Birkhoff map

At every real open gap, the same normalized root family gives a real
theta representative and the rectangular cosine/sine formulas. At closed
gaps both coordinates vanish. Thus the complex sequence map takes real
sources to real coordinate sequences at every finite exponent above one.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal ComplexOrder
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The principal action root is real on the real source locus. -/
theorem sourceNormalizedActionRoot_im_eq_zero_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    (sourceNormalizedActionRoot hp hp1 n ψ).im = 0 := by
  have him := sourceNormalizedActionComplexExtension_im_eq_zero_of_realType hp hp1 n ψ hreal
  have hpos := sourceNormalizedActionComplexExtension_re_pos_of_realType hp hp1 n ψ hreal
  have heq : sourceNormalizedActionComplexExtension hp hp1 n ψ =
      ((sourceNormalizedActionComplexExtension hp hp1 n ψ).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [sourceNormalizedActionRoot,heq]
  have hcast : (4 : ℂ) * ((sourceNormalizedActionComplexExtension hp hp1 n ψ).re : ℂ) =
      ((4 * (sourceNormalizedActionComplexExtension hp hp1 n ψ).re : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast]
  rw [Complex.sqrt_of_nonneg (by exact_mod_cast (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hpos.le))]
  rfl

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- All rectangular coordinates of the actual complex map are real
at real sources, including any number of collapsed gaps. -/
theorem coordinates_im_eq_zero_of_realType
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    ((sourceBirkhoffMap hp hp1 s ψ).1 n).im = 0 ∧
      ((sourceBirkhoffMap hp hp1 s ψ).2 n).im = 0 := by
  have hψ := D.real_subset hreal
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0
  · obtain ⟨hx,hy⟩ := D.real_closed_gap_zero ψ hψ hreal n
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
    rw [hx,hy]
    exact ⟨rfl,rfl⟩
  · obtain ⟨O,V,U,c,T,r,R,z₀,ρ,δ,ε,hψU,_,hδ,E⟩ :=
      D.angular.exists_real_analytic_eta_chart W D.source_open D.source_subset ψ hψ hreal n hgap
    have hβ := D.angular.correction_im_eq_zero_of_realType W D.source_open D.source_subset ψ hψ hreal n
    have hθ := E.theta_representative_im_eq_zero_of_realType
      D.angular.psi.toSourcePsiIsolatingComplexExtension ψ hψU hreal hβ
    have hθeq : sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε ψ =
        ((sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε ψ).re : ℂ) := by
      apply Complex.ext <;> simp [hθ]
    have hξ := sourceNormalizedActionRoot_im_eq_zero_of_realType hp hp1 n ψ hreal
    obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _
      (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n
    have hγ : (sourcePeriodicGapDisplacement hp hp1 ψ n).im = 0 := by
      simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,sub_im,hl,hr,sub_self]
    obtain ⟨hx,hy⟩ := E.birkhoffXY_eq_gap_cos_sin ψ hψU hδ
    rw [(D.coordinates ψ hψ n).1,(D.coordinates ψ hψ n).2,hx,hy,hθeq]
    simp only [← Complex.ofReal_cos,← Complex.ofReal_sin,Complex.mul_im,
      Complex.div_im,Complex.ofReal_im,hξ,hγ,mul_zero,zero_mul,add_zero,zero_sub,zero_div,neg_zero,and_self]

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
