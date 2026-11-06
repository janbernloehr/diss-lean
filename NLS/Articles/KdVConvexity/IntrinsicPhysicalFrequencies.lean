import NLS.Articles.KdVConvexity.PhysicalActionDifferential
import NLS.SequenceSpaces.WeightedNonnegativeAnalyticAtlas

/-! # Intrinsic physical frequencies on the entire original action cone

The frequencies are the derivatives of the independently defined physical
energy, not a new name for arbitrary contour derivatives. Holomorphic
uniqueness from the weighted nonnegative cone proves independence of
every local analytic extension, including at collapsed actions. The larger
ell^(-1,1) domain V0 and its full common-domain identity remain separate.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVConvexity

def PhysicalHstarExtension.originalEnergyAtlas (E : PhysicalHstarExtension) :
    WeightedCoeff.NonnegativeAnalyticAtlas originalPhysicalActionEnergy univ where
  extension := fun _ => E.originalFullEnergy
  analyticAt := fun b _ => E.originalFullEnergy_analytic b (E.originalDomain_contains_cone b)
  agreement := fun _ _ => Eventually.of_forall (fun b => (E.originalFullEnergy_eq_physical b).symm)

/-- An analytic atlas for actual physical action energy; the intrinsic
derivative below is independent of this chosen atlas. -/
def originalPhysicalEnergyAtlas :
    WeightedCoeff.NonnegativeAnalyticAtlas originalPhysicalActionEnergy univ :=
  (Classical.choice nonempty_physicalHstarExtension).originalEnergyAtlas

def originalPhysicalEnergyDifferential
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) : OriginalActionSpace →L[ℂ] ℂ :=
  originalPhysicalEnergyAtlas.derivative b

/-- The paper's physical frequency: derivative of the full physical energy
with respect to the raw original action I_n, with no rescaling by its weight. -/
def originalPhysicalFrequency (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) (n : ℕ+) : ℂ :=
  originalPhysicalEnergyDifferential b
    (WeightedCoeff.single originalActionWeight (actionIndexEquiv.symm n) 1)

/-- Every proved physical Hstar extension gives the same full cotangent
of the actual energy on the original cone. -/
theorem originalPhysicalEnergyDifferential_eq (E : PhysicalHstarExtension)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) :
    originalPhysicalEnergyDifferential b=fderiv ℂ E.originalFullEnergy b.val := by
  exact originalPhysicalEnergyAtlas.derivative_eq (by simp) E.originalEnergyAtlas (mem_univ b)

/-- Even an arbitrary local analytic germ agreeing with physical energy
has the same differential. No interior of the positive cone is assumed. -/
theorem originalPhysicalEnergyDifferential_eq_local_germ
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1)
    (G : OriginalActionSpace → ℂ) (hG : AnalyticAt ℂ G b.val)
    (hrec : (fun c : WeightedCoeff.nonnegativeLocus originalActionWeight 1 => G c.val)
      =ᶠ[𝓝 b] originalPhysicalActionEnergy) :
    originalPhysicalEnergyDifferential b=fderiv ℂ G b.val := by
  let E := Classical.choice nonempty_physicalHstarExtension
  have he := WeightedCoeff.eventuallyEq_of_nonnegative_restriction (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    hG (E.originalFullEnergy_analytic b.val (E.originalDomain_contains_cone b))
    (hrec.trans (E.originalEnergyAtlas.agreement b (mem_univ b)))
  exact (originalPhysicalEnergyDifferential_eq E b).trans he.fderiv_eq.symm

/-- The exact physical frequency identity on the WHOLE original positive
ell^(3,1) action cone, including every zero coordinate and infinite support. -/
theorem originalPhysicalFrequency_eq_gradient (E : PhysicalHstarExtension)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) (n : ℕ+) :
    originalPhysicalFrequency b n = ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)+
      actionGradient E.hamiltonian (originalActionInclusion b.val) n := by
  rw [originalPhysicalFrequency,originalPhysicalEnergyDifferential_eq E b]
  exact E.originalFullEnergy_coordinate_derivative b.val (E.originalDomain_contains_cone b) n

/-- One actual analytic Hilbert-valued map is the renormalized physical
frequency sequence at every point of the full original action cone.
This does not yet assert agreement on the larger V intersect V0 domain. -/
theorem exists_global_analytic_gradient_with_original_physical_frequencies :
    ∃ V : Set ActionSpace, ∃ H : ActionSpace → ℂ, ∃ F : ActionSpace → ActionSpace,
      IsOpen V ∧ positiveQuadrant ⊆ V ∧ AnalyticOnNhd ℂ H V ∧ AnalyticOnNhd ℂ F V ∧
      (∀ a ∈ V, ∀ v : ActionSpace, fderiv ℂ H a v=∑' n : ℕ+, F a n*v n) ∧
      (∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1,
        H (originalActionInclusion b.val)=originalPhysicalHstar b) ∧
      ∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1, ∀ n : ℕ+,
        F (originalActionInclusion b.val) n=
          originalPhysicalFrequency b n-((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ) := by
  let E := Classical.choice nonempty_physicalHstarExtension
  refine ⟨E.domain,E.hamiltonian,actionGradient E.hamiltonian,E.isOpen,E.contains_cone,E.analytic,
    analyticOnNhd_actionGradient _ E.analytic,(fun a _ v => fderiv_eq_tsum_actionGradient _ a v),
    E.physical_agreement,?_⟩
  intro b n
  rw [originalPhysicalFrequency_eq_gradient E b n]
  exact (add_sub_cancel_left _ _).symm

end NLS.Articles.KdVConvexity
