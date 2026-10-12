import NLS.ZakharovShabat.AKNSCoordinates
import NLS.ZakharovShabat.ClassicalIntervalOperator
import NLS.Fourier.IntervalH1Linear

/-! # Classical AKNS domains and the actual differential expression

Equation (1.6) is identified with the AKNS endpoint domains on original
interval H¹ functions. The operator identity uses their actual derivatives
almost everywhere; no differentiability outside the interval is assumed.
-/
noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat

/-- The original AKNS endpoint condition. -/
def aknsBoundaryValue (b : BoundaryCondition) (u : ℂ × ℂ) : ℂ :=
  match b with | .dirichlet => u.2 | .neumann => u.1

/-- The source's classical AKNS interval domain. -/
structure HasAKNSIntervalDomain (b : BoundaryCondition) (g : ℝ → ℂ × ℂ) : Prop where
  fst_regular : HasIntervalH1Regularity (fun x => (g x).1)
  snd_regular : HasIntervalH1Regularity (fun x => (g x).2)
  left : aknsBoundaryValue b (g 0) = 0
  right : aknsBoundaryValue b (g 1) = 0

/-- Regularity of the normalized forward vector change. -/
theorem intervalH1_aknsToZS {g : ℝ → ℂ × ℂ}
    (h₁ : HasIntervalH1Regularity (fun x => (g x).1))
    (h₂ : HasIntervalH1Regularity (fun x => (g x).2)) :
    HasIntervalH1Regularity (fun x => (aknsToZS (g x)).1) ∧
      HasIntervalH1Regularity (fun x => (aknsToZS (g x)).2) := by
  constructor
  · simpa only [aknsToZS, mul_add, mul_assoc] using h₁.linearCombination h₂ aknsScale (aknsScale * Complex.I)
  · simpa only [aknsToZS, sub_eq_add_neg, mul_add, mul_neg, neg_mul, mul_assoc] using
      h₁.linearCombination h₂ aknsScale (-(aknsScale * Complex.I))

/-- Regularity of the inverse vector change. -/
theorem intervalH1_zsToAKNS {f : ℝ → ℂ × ℂ}
    (h₁ : HasIntervalH1Regularity (fun x => (f x).1))
    (h₂ : HasIntervalH1Regularity (fun x => (f x).2)) :
    HasIntervalH1Regularity (fun x => (zsToAKNS (f x)).1) ∧
      HasIntervalH1Regularity (fun x => (zsToAKNS (f x)).2) := by
  constructor
  · simpa only [zsToAKNS, mul_add] using h₁.linearCombination h₂ aknsScale aknsScale
  · simpa only [zsToAKNS, mul_add, mul_assoc] using
      h₁.linearCombination h₂ (aknsScale * (-Complex.I)) (aknsScale * Complex.I)

/-- Both endpoint conditions are exactly transported by T. -/
theorem aknsToZS_boundary_iff (b : BoundaryCondition) (u : ℂ × ℂ) :
    (aknsToZS u).1 = b.extensionSign * (aknsToZS u).2 ↔ aknsBoundaryValue b u = 0 := by
  cases b
  · simpa [BoundaryCondition.extensionSign, aknsBoundaryValue] using aknsToZS_dirichlet_iff u
  · simpa [BoundaryCondition.extensionSign, aknsBoundaryValue] using aknsToZS_neumann_iff u

/-- Exact equivalence with equation (1.6), including original Sobolev regularity. -/
theorem hasClassicalIntervalDomain_aknsToZS_iff (b : BoundaryCondition) (g : ℝ → ℂ × ℂ) :
    b.HasClassicalIntervalDomain (fun x => aknsToZS (g x)) ↔ HasAKNSIntervalDomain b g := by
  constructor
  · intro h
    have hr := intervalH1_zsToAKNS h.fst_regular h.snd_regular
    simp only [zsToAKNS_aknsToZS] at hr
    exact ⟨hr.1, hr.2, (aknsToZS_boundary_iff b _).mp h.left, (aknsToZS_boundary_iff b _).mp h.right⟩
  · intro h
    have hr := intervalH1_aknsToZS h.fst_regular h.snd_regular
    exact ⟨hr.1, hr.2, (aknsToZS_boundary_iff b _).mpr h.left, (aknsToZS_boundary_iff b _).mpr h.right⟩

/-- Every original ZS domain vector has an AKNS-domain inverse. -/
theorem hasAKNSIntervalDomain_zsToAKNS_iff (b : BoundaryCondition) (f : ℝ → ℂ × ℂ) :
    HasAKNSIntervalDomain b (fun x => zsToAKNS (f x)) ↔ b.HasClassicalIntervalDomain f := by
  simpa only [aknsToZS_zsToAKNS] using (hasClassicalIntervalDomain_aknsToZS_iff b (fun x => zsToAKNS (f x))).symm

/-- Actual component derivatives commute with the constant coordinate matrix. -/
theorem deriv_aknsToZS {g : ℝ → ℂ × ℂ} {x : ℝ}
    (h₁ : DifferentiableAt ℝ (fun t => (g t).1) x)
    (h₂ : DifferentiableAt ℝ (fun t => (g t).2) x) :
    (deriv (fun t => (aknsToZS (g t)).1) x, deriv (fun t => (aknsToZS (g t)).2) x) =
      aknsToZS (deriv (fun t => (g t).1) x, deriv (fun t => (g t).2) x) := by
  exact Prod.ext ((h₁.hasDerivAt.add (h₂.hasDerivAt.const_mul Complex.I)).const_mul aknsScale).deriv
    ((h₁.hasDerivAt.sub (h₂.hasDerivAt.const_mul Complex.I)).const_mul aknsScale).deriv

/-- The AKNS operator with actual derivatives. -/
def aknsPhysicalOperator (q p : ℝ → ℂ) (g : ℝ → ℂ × ℂ) (x : ℝ) : ℂ × ℂ :=
  aknsAction (q x) (p x) (g x) (deriv (fun t => (g t).1) x, deriv (fun t => (g t).2) x)

/-- Physical conjugation for arbitrary interval H¹ functions and arbitrary potential representatives. -/
theorem physicalOperator_aknsToZS {g : ℝ → ℂ × ℂ}
    (h₁ : HasIntervalH1Regularity (fun x => (g x).1))
    (h₂ : HasIntervalH1Regularity (fun x => (g x).2)) (q p : ℝ → ℂ) :
    physicalOperator (fun x => aknsPotential (q x) (p x)) (fun x => aknsToZS (g x))
      =ᵐ[volume.restrict (Ioc 0 1)] (fun x => aknsToZS (aknsPhysicalOperator q p g x)) := by
  filter_upwards [h₁.ae_differentiableAt, h₂.ae_differentiableAt] with x hx hy
  change zsAction (aknsPotential (q x) (p x)) (aknsToZS (g x))
    (deriv (fun t => (aknsToZS (g t)).1) x, deriv (fun t => (aknsToZS (g t)).2) x) = _
  rw [deriv_aknsToZS hx hy]
  exact aknsAction_intertwining _ _ _ _

/-- The actual eigenvalue equations are equivalent, in either endpoint domain. -/
theorem akns_eigenEquation_iff (b : BoundaryCondition) {g : ℝ → ℂ × ℂ}
    (hg : HasAKNSIntervalDomain b g) (q p : ℝ → ℂ) (z : ℂ) :
    (physicalOperator (fun x => aknsPotential (q x) (p x)) (fun x => aknsToZS (g x))
      =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • aknsToZS (g x))) ↔
    (aknsPhysicalOperator q p g =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • g x)) := by
  have he := physicalOperator_aknsToZS hg.fst_regular hg.snd_regular q p
  constructor
  · intro h
    filter_upwards [he, h] with x hx hy
    apply aknsCoordinateEquiv.injective
    change aknsToZS (aknsPhysicalOperator q p g x) = aknsCoordinateEquiv (z • g x)
    rw [map_smul]
    exact hx.symm.trans hy
  · intro h
    filter_upwards [he, h] with x hx hy
    rw [hx, hy]
    exact aknsCoordinateEquiv.map_smul z (g x)

/-- A constant smooth Dirichlet vector witnesses the normalization failure in actual derivatives. -/
theorem physicalOperator_printed_akns_normalization_false :
    physicalOperator (fun _ => aknsToZS (1,0)) (fun _ => aknsToZS (1,0)) 0 ≠
      aknsToZS (aknsPhysicalOperator (fun _ => 1) (fun _ => 0) (fun _ => (1,0)) 0) := by
  simpa [physicalOperator, aknsPhysicalOperator, aknsToZS, zsAction, aknsAction] using
    aknsAction_printed_normalization_false

end NLS.ZakharovShabat
