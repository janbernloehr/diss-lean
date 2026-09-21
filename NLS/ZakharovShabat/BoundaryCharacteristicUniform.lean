import NLS.ZakharovShabat.UniformBoundaryDisplacementBounds
import NLS.ZakharovShabat.SingleSpectralProductFamilies
import NLS.ZakharovShabat.CanonicalBoundaryCharacteristic

/-!
# Intrinsic boundary products uniform over potential neighborhoods
Bounded complete labels identify all large intrinsic polynomials with the
uniformly convergent full products. One neighborhood works for both boundary
conditions and every compact set of spectral parameters.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Common counted labels and bounded displacements give uniform intrinsic boundary convergence. -/
theorem tendstoUniformlyOn_boundaryCharacteristic_family {X : Type*} (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : X → dirichletSubspace (p := p)) (N : ℕ) (ξ : X → ℤ → ℂ)
    (hξ : ∀ x, BoundaryRootLabeling b hp (φ x).val (φ x).property N (ξ x))
    (R : ℝ) (hR : 0 ≤ R) (hb : ∀ x, ‖(⟨_,(hξ x).displacement⟩ : Coeff p)‖ ≤ R)
    (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun M (t : ℂ × X) => b.normalizedCentralPolynomial hp (φ t.2).val (φ t.2).property M t.1)
      (fun t => b.characteristic hp (φ t.2).val (φ t.2).property t.1) atTop (K ×ˢ univ) := by
  have h := tendstoUniformlyOn_boundaryCharacteristicProduct_family hp hp1 ξ
    (fun x => (hξ x).displacement) univ R hR (fun x _ => hb x) K hK
  have ht : TendstoUniformlyOn (fun M (t : ℂ × X) => boundaryCharacteristicPartialProduct (ξ t.2) t.1 M)
      (fun t => b.characteristic hp (φ t.2).val (φ t.2).property t.1) atTop (K ×ˢ univ) :=
    h.congr_right (fun t _ => congrFun (hξ t.2).product_eq_characteristic t.1)
  apply ht.congr
  filter_upwards [eventually_ge_atTop N] with M hM t _
  exact (hξ t.2).cutoff_eq_normalizedCentral M hM t.1

/-- Both intrinsic boundary characteristics are uniform polynomial limits on one potential neighborhood. -/
theorem exists_uniform_boundaryCharacteristic (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : dirichletSubspace (p := p)) :
    ∃ U : Set (dirichletSubspace (p := p)), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ b : BoundaryCondition, ∀ K : Set ℂ, IsCompact K →
        TendstoUniformlyOn (fun M (t : ℂ × dirichletSubspace (p := p)) =>
          b.normalizedCentralPolynomial hp t.2.val t.2.property M t.1)
          (fun t => b.characteristic hp t.2.val t.2.property t.1) atTop (K ×ˢ U) := by
  obtain ⟨N,_,U,ho,hc,hφ,h0,R,hR,h⟩ := exists_uniform_bounded_boundaryRootLabeling hp hp1 φ
  refine ⟨U,ho,hc,hφ,h0,?_⟩
  intro b K hK
  choose ξ hξ hb using (fun ψ : U => h ψ.val ψ.property b)
  apply NLS.ComplexAnalysis.tendstoUniformlyOn_prod_of_subtype
  exact tendstoUniformlyOn_boundaryCharacteristic_family hp hp1 b Subtype.val N ξ hξ R hR hb K hK

end NLS.ZakharovShabat
