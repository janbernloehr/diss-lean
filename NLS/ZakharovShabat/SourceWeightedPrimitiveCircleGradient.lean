import NLS.ZakharovShabat.SourceLaurentActionAnalytic
import NLS.ZakharovShabat.SourceFullAbelianDifferentialData

/-! # Weighted contour derivatives at every complex source

This differentiates the actual full primitive on its open joint moving-cut
complement. A Laurent weight need only avoid zero on the circuit itself;
there is no unspoken zero-excluding-disc hypothesis in this derivative.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceFullAbelianDifferentialData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W U : Set (CoeffPair p)}

theorem fderiv_weightedPrimitiveCircle (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (n : ℤ) (φ : CoeffPair p) (hφ : φ ∈ U) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (w : ℂ → ℂ) (O : Set ℂ) (hO : IsOpen O) (hw : AnalyticOnNhd ℂ w O)
    (hcircle : sphere c R ⊆ O) (v : CoeffPair p) :
    (fderiv ℂ (fun ψ => sourceWeightedPrimitiveCircle hp hp1 W n ψ c R w) φ) v =
      -(Real.pi:ℂ)⁻¹ * ∮ z in C(c,R),
        w z * ((sourceCanonicalRoot hp hp1 φ z)⁻¹ * sourceDiscriminantCotangent hp z φ v) := by
  let A := sourceCanonicalRootJointDomain hp hp1 U ∩ Prod.fst ⁻¹' O
  let F : ℂ × CoeffPair p → ℂ := fun t => w t.1*sourceFullAbelianPrimitive hp hp1 W n t
  have hA : IsOpen A := D.root_domain_open.inter (hO.preimage continuous_fst)
  have hF : AnalyticOnNhd ℂ F A := by
    intro t ht
    exact ((hw t.1 ht.2).comp analyticAt_fst).mul (D.analytic n t ht.1)
  have hφc (z : ℂ) (hz : z ∈ sphere c R) : (z,φ) ∈ A := ⟨⟨hφ,hc hz⟩,hcircle hz⟩
  obtain ⟨V,hV,hφV,M,_,hb⟩ := exists_uniform_joint_fderiv_bound_on_circle F A hA hF c R φ hφc
  have hd (ψ : CoeffPair p) (hψ : ψ ∈ V) (θ : ℝ) : (circleMap c R θ,ψ) ∈ A :=
    (hb _ (circleMap_mem_sphere c hR θ) ψ hψ).1
  have hbound (ψ : CoeffPair p) (hψ : ψ ∈ V) (θ : ℝ) :
      ‖fderiv ℂ F (circleMap c R θ,ψ)‖ ≤ M := (hb _ (circleMap_mem_sphere c hR θ) ψ hψ).2
  have hi := differentiableAt_circleIntegral_of_jointAnalytic F A hA hF c R hR V hV φ hφV M hd hbound
  have hf := fderiv_circleIntegral_apply_of_jointAnalytic F A hA hF c R hR V hV φ hφV M hd hbound v
  change (fderiv ℂ (fun ψ => -(Real.pi:ℂ)⁻¹ * ∮ z in C(c,R), F (z,ψ)) φ) v = _
  rw [fderiv_const_mul hi,smul_apply,smul_eq_mul,hf]
  congr 1
  apply circleIntegral.integral_congr hR
  intro z hz
  dsimp only [F]
  rw [fderiv_const_mul (D.source_hasFDerivAt n z φ hφ (hc hz)).differentiableAt,
    smul_apply,smul_eq_mul,D.source_fderiv n z φ hφ (hc hz),smul_apply,smul_eq_mul]

theorem fderiv_laurentPrimitiveCircle (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (n k : ℤ) (φ : CoeffPair p) (hφ : φ ∈ U) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ) (hzero : (0:ℂ) ∉ sphere c R)
    (v : CoeffPair p) :
    (fderiv ℂ (fun ψ => sourceLaurentPrimitiveCircle hp hp1 W n k ψ c R) φ) v =
      -(Real.pi:ℂ)⁻¹ * ∮ z in C(c,R),
        z^(k-1) * ((sourceCanonicalRoot hp hp1 φ z)⁻¹ * sourceDiscriminantCotangent hp z φ v) := by
  exact D.fderiv_weightedPrimitiveCircle n φ hφ c R hR hc (fun z => z^(k-1))
    {z | z ≠ 0} isOpen_compl_singleton (fun z hz => analyticAt_id.zpow hz)
    (fun z hz he => hzero (he ▸ hz)) v

end SourceFullAbelianDifferentialData
end NLS.ZakharovShabat
