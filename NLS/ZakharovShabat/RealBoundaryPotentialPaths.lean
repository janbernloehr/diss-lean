import NLS.ZakharovShabat.CanonicalBoundaryContinuity
import NLS.ZakharovShabat.RealPotentialPaths
import NLS.ZakharovShabat.PhysicalParityMonodromy

/-! # Real boundary paths compatible with the original periodic path
Real scaling preserves the reflected boundary space and gives continuous
canonical roots. A common physical representative remains common after
scaling, allowing comparison with the original periodic endpoints.
-/

noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The reflected boundary-potential path obtained by real scaling. -/
def realBoundaryPotentialPath (ψ : dirichletSubspace (p := p)) (t : ℝ) : dirichletSubspace (p := p) :=
  (t : ℂ) • ψ

@[simp] theorem realBoundaryPotentialPath_zero (ψ : dirichletSubspace (p := p)) :
    realBoundaryPotentialPath ψ 0 = 0 := by simp [realBoundaryPotentialPath]

@[simp] theorem realBoundaryPotentialPath_one (ψ : dirichletSubspace (p := p)) :
    realBoundaryPotentialPath ψ 1 = ψ := by simp [realBoundaryPotentialPath]

/-- Scaling varies continuously within the actual reflected boundary space. -/
theorem continuous_realBoundaryPotentialPath (ψ : dirichletSubspace (p := p)) :
    Continuous (realBoundaryPotentialPath ψ) := continuous_ofReal.smul continuous_const

/-- Every scaled reflected potential remains real type. -/
theorem realBoundaryPotentialPath_isRealType (ψ : dirichletSubspace (p := p))
    (hψ : IsRealType ψ.val) (t : ℝ) : IsRealType (realBoundaryPotentialPath ψ t).val := hψ.ofReal_smul t

/-- Each canonical boundary root moves continuously along the whole real scaling path. -/
theorem continuous_canonicalBoundaryRoots_realBoundaryPotentialPath (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (ψ : dirichletSubspace (p := p)) (hψ : IsRealType ψ.val) (n : ℤ) :
    Continuous (fun t : ℝ => b.canonicalRoots hp hp1 (realBoundaryPotentialPath ψ t).val
      (realBoundaryPotentialPath ψ t).property n) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (continuousAt_canonicalBoundaryRoots_of_realType hp hp1 b (realBoundaryPotentialPath ψ t)
    (realBoundaryPotentialPath_isRealType ψ hψ t) n).comp (continuous_realBoundaryPotentialPath ψ).continuousAt

/-- The left periodic endpoint is continuous on its real scaling path. -/
theorem continuous_canonicalPeriodicLeft_realPotentialPath (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hφ : IsRealType φ.val) (n : ℤ) :
    Continuous (fun t : ℝ => canonicalPeriodicLeft hp hp1 (realPotentialPath φ t).val
      (realPotentialPath φ t).property n) := by
  simpa only [canonicalPeriodicSlot_left] using
    continuous_canonicalPeriodicSlot_realPotentialPath hp hp1 φ hφ (toLex (n,0))

/-- The right periodic endpoint is continuous on its real scaling path. -/
theorem continuous_canonicalPeriodicRight_realPotentialPath (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hφ : IsRealType φ.val) (n : ℤ) :
    Continuous (fun t : ℝ => canonicalPeriodicRight hp hp1 (realPotentialPath φ t).val
      (realPotentialPath φ t).property n) := by
  simpa only [canonicalPeriodicSlot_right] using
    continuous_canonicalPeriodicSlot_realPotentialPath hp hp1 φ hφ (toLex (n,1))

/-- Scaling the coefficient and continuous potentials preserves their exact agreement on the original interval. -/
theorem physicalBase_smul_eq_extend (c : ℂ) (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) :
    physicalBase (c • φ) =ᵐ[volume.restrict (Ioc 0 1)] extend (c • Φ) := by
  have hs : physicalBase (c • φ) =ᵐ[volume.restrict (Ioc 0 1)] (fun x => c • physicalBase φ x) :=
    ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num)) (physicalBase_smul c φ)
  filter_upwards [hs,hΦ] with x hx hφx
  rw [hx,hφx]
  rfl

/-- Pointwise real type of a continuous physical representative is preserved by real scaling. -/
theorem realType_curve_ofReal_smul (Φ : Curve (ℂ × ℂ))
    (hΦ : ∀ s, (Φ s).2 = conj (Φ s).1) (t : ℝ) :
    ∀ s, (((t : ℂ) • Φ) s).2 = conj (((t : ℂ) • Φ) s).1 := by
  intro s
  change (t : ℂ)*(Φ s).2 = conj ((t : ℂ)*(Φ s).1)
  rw [map_mul,conj_ofReal,hΦ s]

end NLS.ZakharovShabat
