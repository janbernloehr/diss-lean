import NLS.ZakharovShabat.SourceAbelianJointExtension
import NLS.ZakharovShabat.SourceRealTypeProjection

/-! # Compatible abelian charts across spectral and source anchors

A chart records a product ball on which the actual normalization and
joint differential hold. Two such charts agree on their entire overlap,
including at complex sources and with different real-source anchors.
The contractive real projection supplies a common real-source point;
equality of joint derivatives propagates its normalization over the
convex overlap.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A product chart carrying all indexed abelian integrals, their joint
differentials, and their agreement with actual real-source values. -/
structure SourceAbelianJointChart (hp : p ≠ ⊤) (hp1 : 1 < p) where
  source : realTypeSourceSubmodule p
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  root_domain : ∀ t ∈ Metric.ball center radius ×ˢ Metric.ball source.val radius,
    t.1 ∈ sourceCanonicalRootDomain hp hp1 t.2
  analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceAbelianLogChart hp hp1 source.val source.property center n)
    (Metric.ball center radius ×ˢ Metric.ball source.val radius)
  hasFDerivAt : ∀ (n : ℤ) t, t ∈ Metric.ball center radius ×ˢ Metric.ball source.val radius →
    HasFDerivAt (sourceAbelianLogChart hp hp1 source.val source.property center n)
      ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t
  real_eq : ∀ (n : ℤ) (ψ : realTypeSourceSubmodule p), ψ.val ∈ Metric.ball source.val radius →
    ∀ z ∈ Metric.ball center radius,
      sourceAbelianLogChart hp hp1 source.val source.property center n (z,ψ.val) =
        sourceAbelianPrimitive hp hp1 ψ.val ψ.property z+I*(Real.pi : ℂ)*n

/-- Every real source and every off-cut spectral point admits such a chart. -/
theorem exists_sourceAbelianJointChart (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (a : ℂ) (ha : a ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    ∃ D : SourceAbelianJointChart hp hp1, D.source = φ ∧ D.center = a := by
  obtain ⟨r,hr,hroot,hcharts⟩ := exists_sourceAbelianLogChart_product hp hp1 φ a ha
  exact ⟨⟨φ,a,r,hr,hroot,fun n => (hcharts n).1,
    fun n => (hcharts n).2.1,fun n => (hcharts n).2.2⟩,rfl,rfl⟩

namespace SourceAbelianJointChart
variable {hp : p ≠ ⊤} {hp1 : 1 < p}

def domain (D : SourceAbelianJointChart hp hp1) : Set (ℂ × CoeffPair p) :=
  Metric.ball D.center D.radius ×ˢ Metric.ball D.source.val D.radius

def toFun (D : SourceAbelianJointChart hp hp1) (n : ℤ) : ℂ × CoeffPair p → ℂ :=
  sourceAbelianLogChart hp hp1 D.source.val D.source.property D.center n

theorem isOpen_domain (D : SourceAbelianJointChart hp hp1) : IsOpen D.domain :=
  Metric.isOpen_ball.prod Metric.isOpen_ball

theorem convex_domain (D : SourceAbelianJointChart hp hp1) : Convex ℝ D.domain :=
  (convex_ball D.center D.radius).prod (convex_ball D.source.val D.radius)

theorem center_mem (D : SourceAbelianJointChart hp hp1) : (D.center,D.source.val) ∈ D.domain :=
  ⟨Metric.mem_ball_self D.radius_pos,Metric.mem_ball_self D.radius_pos⟩

/-- Projecting a source to its real part keeps it in a ball centered
at a real source, and leaves the spectral coordinate unchanged. -/
theorem real_projection_mem (D : SourceAbelianJointChart hp hp1) (t : ℂ × CoeffPair p)
    (ht : t ∈ D.domain) : (t.1,(sourceRealTypeProjection hp t.2).val) ∈ D.domain := by
  refine ⟨ht.1,?_⟩
  have hd := (lipschitzWith_sourceRealPart hp).dist_le_mul t.2 D.source.val
  have hfix : sourceRealPart D.source.val = D.source.val :=
    sourceRealTypeProjection_val_of_realType hp D.source.val D.source.property
  simp only [NNReal.coe_one,one_mul,hfix] at hd
  exact hd.trans_lt ht.2

/-- Charts anchored at different spectral points and different real
potentials agree at every complex-source point of their overlap. -/
theorem eqOn_overlap (D E : SourceAbelianJointChart hp hp1) (n : ℤ) :
    EqOn (D.toFun n) (E.toFun n) (D.domain ∩ E.domain) := by
  intro t ht
  let ψ := sourceRealTypeProjection hp t.2
  have hD := D.real_projection_mem t ht.1
  have hE := E.real_projection_mem t ht.2
  have hbase : (t.1,ψ.val) ∈ D.domain ∩ E.domain := ⟨hD,hE⟩
  have he : D.toFun n (t.1,ψ.val) = E.toFun n (t.1,ψ.val) :=
    (D.real_eq n ψ hD.2 t.1 hD.1).trans (E.real_eq n ψ hE.2 t.1 hE.1).symm
  exact (D.isOpen_domain.inter E.isOpen_domain).eqOn_of_fderiv_eq
    (D.convex_domain.inter E.convex_domain).isPreconnected
    ((D.analytic n).differentiableOn.mono inter_subset_left)
    ((E.analytic n).differentiableOn.mono inter_subset_right)
    (fun u hu => (D.hasFDerivAt n u hu.1).fderiv.trans (E.hasFDerivAt n u hu.2).fderiv.symm)
    hbase he ht

end SourceAbelianJointChart
end NLS.ZakharovShabat
