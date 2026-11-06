import NLS.Articles.KdVConvexity.PhysicalActionHamiltonian
import NLS.Articles.KdVConvexity.ActionDifferential
import NLS.Articles.KdVConvexity.OriginalActionLinearEnergy

/-! # Differentiating actual physical KdV energy in the original actions

The full energy is independently defined by physical H1 representatives.
Its analytic extension to the original weighted Banach space is obtained
by restoring the exact bounded linear energy. No KdV frequency or Taylor
coefficient is assumed. Extension to the larger ell^(-1,1) frequency domain
and the minus-six Taylor coefficient remain separate obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

/-- Full physical energy on the entire original positive action cone. -/
def originalPhysicalActionEnergy (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) : ℂ :=
  physicalActionHamiltonian
    ⟨originalActionInclusion b.val,originalActionInclusion_mem_domain b.val b.property⟩

theorem originalPhysicalActionEnergy_eq_source
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1)
    (q : RealHillWeightedPotential hillH1SpectralWeight) (hm : q.val.val 0=0)
    (ha : physicalHilbertActions hillH1SpectralWeight q=originalActionInclusion b.val) :
    originalPhysicalActionEnergy b =
      classicalHamiltonian (fun x : ℝ => hillNativeH1Continuous q.val (x : AddCircle (2 : ℝ))) := by
  rw [originalPhysicalActionEnergy,physicalActionHamiltonian_eq_source _ q hm ha,
    hillNativeH1Hamiltonian_eq_physical_integral]

/-- The data in this record exist unconditionally by the proved global
physical extension theorem. They merely retain its domain and function. -/
structure PhysicalHstarExtension where
  domain : Set ActionSpace
  hamiltonian : ActionSpace → ℂ
  isOpen : IsOpen domain
  contains_cone : positiveQuadrant ⊆ domain
  analytic : AnalyticOnNhd ℂ hamiltonian domain
  physical_agreement : ∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1,
    hamiltonian (originalActionInclusion b.val)=originalPhysicalHstar b

theorem nonempty_physicalHstarExtension : Nonempty PhysicalHstarExtension := by
  obtain ⟨V,H,hV,hcone,hH,hphysical⟩ := exists_global_analytic_extension_of_original_physical_Hstar
  exact ⟨⟨V,H,hV,hcone,hH,hphysical⟩⟩

namespace PhysicalHstarExtension

def originalDomain (E : PhysicalHstarExtension) : Set OriginalActionSpace :=
  originalActionInclusion ⁻¹' E.domain

def originalFullEnergy (E : PhysicalHstarExtension) (b : OriginalActionSpace) : ℂ :=
  E.hamiltonian (originalActionInclusion b)+originalActionLinearEnergy b

theorem originalDomain_open (E : PhysicalHstarExtension) : IsOpen E.originalDomain :=
  E.isOpen.preimage originalActionInclusion.continuous

theorem originalDomain_contains_cone (E : PhysicalHstarExtension)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) : b.val ∈ E.originalDomain :=
  E.contains_cone (originalActionInclusion_mem_domain b.val b.property).1

theorem originalFullEnergy_analytic (E : PhysicalHstarExtension) :
    AnalyticOnNhd ℂ E.originalFullEnergy E.originalDomain := by
  intro b hb
  exact ((E.analytic _ hb).comp (originalActionInclusion.analyticAt b)).add
    (originalActionLinearEnergy.analyticAt b)

theorem originalFullEnergy_eq_physical (E : PhysicalHstarExtension)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) :
    E.originalFullEnergy b.val=originalPhysicalActionEnergy b := by
  rw [originalFullEnergy,E.physical_agreement,originalPhysicalHstar,
    physicalRenormalizedActionHamiltonian,←originalActionLinearEnergy_eq_tsum]
  exact sub_add_cancel _ _

/-- The full physical cotangent, on every direction in the original
weighted Banach space, is the pullback of the Hilbert differential plus
the original homogeneous linear energy. -/
theorem originalFullEnergy_hasFDerivAt (E : PhysicalHstarExtension)
    (b : OriginalActionSpace) (hb : b ∈ E.originalDomain) :
    HasFDerivAt E.originalFullEnergy
      (((fderiv ℂ E.hamiltonian (originalActionInclusion b)).comp originalActionInclusion)+
        originalActionLinearEnergy) b :=
  ((E.analytic _ hb).differentiableAt.hasFDerivAt.comp b originalActionInclusion.hasFDerivAt).add
    originalActionLinearEnergy.hasFDerivAt

/-- Literal coordinate derivative of the full energy, retaining the raw
action amplitude one at n, also when that action is zero. -/
theorem originalFullEnergy_coordinate_derivative (E : PhysicalHstarExtension)
    (b : OriginalActionSpace) (hb : b ∈ E.originalDomain) (n : ℕ+) :
    fderiv ℂ E.originalFullEnergy b
      (WeightedCoeff.single originalActionWeight (actionIndexEquiv.symm n) 1) =
        ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)+
          actionGradient E.hamiltonian (originalActionInclusion b) n := by
  rw [(E.originalFullEnergy_hasFDerivAt b hb).fderiv]
  change fderiv ℂ E.hamiltonian (originalActionInclusion b)
      (originalActionInclusion (WeightedCoeff.single originalActionWeight (actionIndexEquiv.symm n) 1))+
    originalActionLinearEnergy (WeightedCoeff.single originalActionWeight (actionIndexEquiv.symm n) 1)=_
  rw [originalActionInclusion_single,originalActionLinearEnergy_single,mul_one,actionGradient_apply]
  exact add_comm _ _

theorem originalFullEnergy_line_hasDerivAt (E : PhysicalHstarExtension)
    (b : OriginalActionSpace) (hb : b ∈ E.originalDomain) (n : ℕ+) :
    HasDerivAt (fun z : ℂ => E.originalFullEnergy
      (b+z • WeightedCoeff.single originalActionWeight (actionIndexEquiv.symm n) 1))
      (((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)+
        actionGradient E.hamiltonian (originalActionInclusion b) n) 0 := by
  have hline : HasDerivAt (fun z : ℂ =>
      b+z • WeightedCoeff.single originalActionWeight (actionIndexEquiv.symm n) 1)
      (WeightedCoeff.single originalActionWeight (actionIndexEquiv.symm n) 1) 0 := by
    simpa only [id_eq,one_smul] using
      ((hasDerivAt_id (0 : ℂ)).smul_const
        (WeightedCoeff.single originalActionWeight (actionIndexEquiv.symm n) 1)).const_add b
  have h := ((E.originalFullEnergy_analytic b hb).differentiableAt.hasFDerivAt).comp_hasDerivAt_of_eq
    0 hline (by simp)
  rwa [E.originalFullEnergy_coordinate_derivative b hb n] at h

end PhysicalHstarExtension
end NLS.Articles.KdVConvexity
