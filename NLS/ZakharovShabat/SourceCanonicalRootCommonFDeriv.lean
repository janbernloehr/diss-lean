import NLS.ZakharovShabat.SourceEquation2_15
import NLS.ZakharovShabat.SourceCanonicalRootSourceFDeriv
import NLS.ZakharovShabat.SourceDiscriminantMixedDerivative

/-!
# Canonical-root derivatives on the retained common domain

Differentiate the square identity on the original open joint domain.
Both source and spectral derivatives follow at every complex source in W;
no real-base hypothesis or replacement source neighborhood is needed.
-/

noncomputable section
open Set NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The square identity determines the full joint Fréchet derivative. -/
theorem SourceEquation2_15Data.root_joint_fderiv
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_15Data hp hp1 W) (t : ℂ × CoeffPair p)
    (ht : t ∈ sourceCanonicalRootJointDomain hp hp1 W) (v : ℂ × CoeffPair p) :
    (fderiv ℂ (sourceCanonicalRootJointProduct hp hp1) t) v =
      canonicalDiscriminant hp (periodOnePotential t.2) t.1 / sourceCanonicalRoot hp hp1 t.2 t.1 *
        (fderiv ℂ (fun q : ℂ × CoeffPair p =>
          canonicalDiscriminant hp (periodOnePotential q.2) q.1) t) v := by
  exact fderiv_squareRoot_of_sq_eq_discriminant_sq_sub_four
    (sourceCanonicalRootJointProduct hp hp1)
    (fun q : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential q.2) q.1)
    _ H.joint.1 (fun q hq => sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 q.2 q.1 hq.2)
    t ht (H.previous.previous.previous.joint.2 t ht).differentiableAt
    (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 t (mem_univ _)).differentiableAt
    (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 t.2 t.1 ht.2) v

/-- The source derivative formula holds at every complex source in W. -/
theorem SourceEquation2_15Data.root_source_fderiv
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_15Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) (v : CoeffPair p) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourceCanonicalRoot hp hp1 ψ z) φ) v =
      canonicalDiscriminant hp (periodOnePotential φ) z / sourceCanonicalRoot hp hp1 φ z *
        (fderiv ℂ (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ) v := by
  let Q := sourceCanonicalRootJointProduct hp hp1
  let Δ : ℂ × CoeffPair p → ℂ := fun t => canonicalDiscriminant hp (periodOnePotential t.2) t.1
  have hQ : DifferentiableAt ℂ Q (z,φ) :=
    (H.previous.previous.previous.joint.2 (z,φ) ⟨hφ,hz⟩).differentiableAt
  have hΔ : DifferentiableAt ℂ Δ (z,φ) :=
    (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,φ) (mem_univ _)).differentiableAt
  change (fderiv ℂ (fun ψ => Q (z,ψ)) φ) v = Δ (z,φ)/Q (z,φ)*(fderiv ℂ (fun ψ => Δ (z,ψ)) φ) v
  rw [fderiv_source_section_eq_joint Q z φ hQ,fderiv_source_section_eq_joint Δ z φ hΔ]
  exact H.root_joint_fderiv (z,φ) ⟨hφ,hz⟩ (0,v)

/-- The spectral derivative uses the same joint square identity. -/
theorem SourceEquation2_15Data.root_spectral_deriv
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_15Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    deriv (sourceCanonicalRoot hp hp1 φ) z =
      canonicalDiscriminant hp (periodOnePotential φ) z / sourceCanonicalRoot hp hp1 φ z *
        deriv (canonicalDiscriminant hp (periodOnePotential φ)) z := by
  let Q := sourceCanonicalRootJointProduct hp hp1
  let Δ : ℂ × CoeffPair p → ℂ := fun t => canonicalDiscriminant hp (periodOnePotential t.2) t.1
  have hQ : DifferentiableAt ℂ Q (z,φ) :=
    (H.previous.previous.previous.joint.2 (z,φ) ⟨hφ,hz⟩).differentiableAt
  have hΔ : DifferentiableAt ℂ Δ (z,φ) :=
    (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,φ) (mem_univ _)).differentiableAt
  change deriv (fun w => Q (w,φ)) z = Δ (z,φ)/Q (z,φ)*deriv (fun w => Δ (w,φ)) z
  rw [deriv_spectral_section_eq_fderiv Q z φ hQ,deriv_spectral_section_eq_fderiv Δ z φ hΔ]
  exact H.root_joint_fderiv (z,φ) ⟨hφ,hz⟩ (1,0)

end NLS.ZakharovShabat
