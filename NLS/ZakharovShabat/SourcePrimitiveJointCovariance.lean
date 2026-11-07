import NLS.ZakharovShabat.SourcePrimitiveJointConnected
import Mathlib.Analysis.Calculus.MeanValue

/-! # Primitive covariance from the actual full joint differential

A signed joint linear symmetry fixes the derivative of the transformed
primitive. Connectedness of the entire moving-cut domain and the actual
zero-source normalization fix the additive constant, without a new logarithm
branch or an assumed primitive-value symmetry.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceFullAbelianDifferentialData.primitive_covariance
    {hp : p ≠ ⊤} {hp1 : 1 < p} {A V : Set (CoeffPair p)}
    (D : SourceFullAbelianDifferentialData hp hp1 A V) (hV : IsConnected V)
    (B : (ℂ × CoeffPair p) →L[ℂ] (ℂ × CoeffPair p)) (ε : ℂ) (hε : ε*ε = 1)
    (hB : MapsTo B (sourceCanonicalRootJointDomain hp hp1 V) (sourceCanonicalRootJointDomain hp hp1 V))
    (hΔ : ∀ t : ℂ × CoeffPair p,
      canonicalDiscriminant hp (periodOnePotential (B t).2) (B t).1 =
        canonicalDiscriminant hp (periodOnePotential t.2) t.1)
    (hr : ∀ t : ℂ × CoeffPair p,
      sourceCanonicalRoot hp hp1 (B t).2 (B t).1 = ε*sourceCanonicalRoot hp hp1 t.2 t.1)
    (hB0 : ∀ z : ℂ, B (z,0) = (ε*z,0)) :
    ∀ t ∈ sourceCanonicalRootJointDomain hp hp1 V,
      sourceFullAbelianPrimitive hp hp1 A 0 (B t) = ε*sourceFullAbelianPrimitive hp hp1 A 0 t := by
  let F := sourceFullAbelianPrimitive hp hp1 A 0
  let δ : ℂ × CoeffPair p → ℂ := fun t => canonicalDiscriminant hp (periodOnePotential t.2) t.1
  have hδ : AnalyticOnNhd ℂ δ univ := analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
  have hεinv : ε⁻¹ = ε := inv_eq_of_mul_eq_one_left hε
  have hc (t : ℂ × CoeffPair p) (ht : t ∈ sourceCanonicalRootJointDomain hp hp1 V) :
      HasFDerivAt (fun q => F (B q))
        (ε • ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ • fderiv ℂ δ t)) t := by
    have hd := (hδ (B t) (mem_univ _)).differentiableAt.hasFDerivAt.comp t B.hasFDerivAt
    have heq : (fun q => δ (B q)) = δ := funext hΔ
    change HasFDerivAt (fun q => δ (B q)) ((fderiv ℂ δ (B t)).comp B) t at hd
    rw [heq] at hd
    have hdc := hd.fderiv.symm
    have he : (((sourceCanonicalRoot hp hp1 (B t).2 (B t).1)⁻¹ • fderiv ℂ δ (B t)).comp B) =
        ε • ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ • fderiv ℂ δ t) := by
      apply ContinuousLinearMap.ext
      intro v
      change (sourceCanonicalRoot hp hp1 (B t).2 (B t).1)⁻¹*(fderiv ℂ δ (B t)) (B v) =
        ε*((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹*(fderiv ℂ δ t) v)
      have hh := congrArg (fun L => L v) hdc
      change (fderiv ℂ δ (B t)) (B v) = (fderiv ℂ δ t) v at hh
      rw [hh,hr,mul_inv_rev,hεinv]
      ring
    have h := (D.differential 0 (B t) (hB ht)).comp t B.hasFDerivAt
    change HasFDerivAt (fun q => F (B q))
      (((sourceCanonicalRoot hp hp1 (B t).2 (B t).1)⁻¹ • fderiv ℂ δ (B t)).comp B) t at h
    rwa [he] at h
  have hg (t : ℂ × CoeffPair p) (ht : t ∈ sourceCanonicalRootJointDomain hp hp1 V) :
      HasFDerivAt (fun q => ε*F q)
        (ε • ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ • fderiv ℂ δ t)) t :=
    (D.differential 0 t ht).const_smul ε
  have hz : (0 : CoeffPair p) ∈ V := D.real_subset (by simp [realTypeSourceLocus])
  obtain ⟨E⟩ := D.charts 0 hz
  obtain ⟨z,hzroot⟩ := (E.discs.isConnected_rootDomain 0 E.source_mem).nonempty
  have ht0 : (z,0) ∈ sourceCanonicalRootJointDomain hp hp1 V := ⟨hz,hzroot⟩
  have hbase : F (B (z,0)) = ε*F (z,0) := by
    rw [hB0]
    simp only [F,sourceFullAbelianPrimitive_zero E,Int.cast_zero,mul_zero,add_zero]
    ring
  exact D.root_domain_open.eqOn_of_fderiv_eq (D.isConnected_jointDomain hV).isPreconnected
    (fun t ht => (hc t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hg t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hc t ht).fderiv.trans (hg t ht).fderiv.symm) ht0 hbase

end NLS.ZakharovShabat
