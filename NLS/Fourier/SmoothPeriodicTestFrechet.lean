import NLS.Fourier.PeriodicDistributionFourierGrowth
import Mathlib.Topology.Metrizable.Uniformity
/-! # Completeness of the original smooth periodic test space

The derivative map identifies the test space with a closed subspace of a
countable product of Banach spaces. This proves completeness, metrizability,
and local convexity for the topology of the exact physical C^N norms.
-/
noncomputable section
open Set Filter Topology
open scoped SchwartzMap BoundedContinuousFunction ContDiff
namespace NLS.Fourier.SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

abbrev DerivativeJet := ℕ → (ℝ →ᵇ ℂ)

def derivativeJet : SmoothPeriodicTest L →ₗ[ℂ] DerivativeJet :=
  LinearMap.pi (fun k => derivative (Fact.out : 0 < L).ne' k)

def CompatibleJet (L : ℝ) (g : DerivativeJet) : Prop :=
  Function.Periodic (g 0) L ∧ ∀ k : ℕ, ∀ x : ℝ, HasDerivAt (g k) (g (k+1) x) x

omit [Fact (0 < L)] in
theorem isClosed_compatibleJet : IsClosed {g : DerivativeJet | CompatibleJet L g} := by
  apply isClosed_iff_forall_filter.mpr
  intro g l hl hm ht
  let : l.NeBot := hl
  have he : ∀ᶠ a in l, CompatibleJet L a := Filter.le_principal_iff.mp hm
  have hu (k : ℕ) : TendstoUniformly (fun a : DerivativeJet => (a k : ℝ → ℂ)) (g k) l :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp ((continuous_apply k).tendsto g |>.mono_left ht)
  refine ⟨fun x => ?_,fun k x => ?_⟩
  · exact tendsto_nhds_unique_of_eventuallyEq ((hu 0).tendsto_at (x+L)) ((hu 0).tendsto_at x)
      (he.mono (fun a ha => ha.1 x))
  · exact hasDerivAt_of_tendstoUniformly (hu (k+1)) (he.mono (fun a ha => ha.2 k)) (fun x => (hu k).tendsto_at x) x

theorem derivativeJet_compatible (f : SmoothPeriodicTest L) : CompatibleJet L (derivativeJet f) := by
  refine ⟨f.periodic,fun k x => ?_⟩
  change HasDerivAt (iteratedDeriv k (f : ℝ → ℂ)) (iteratedDeriv (k+1) (f : ℝ → ℂ) x) x
  rw [iteratedDeriv_succ]
  exact ((contDiff_infty.mp (f.smooth_deriv k) 1).differentiable (by norm_num)).differentiableAt.hasDerivAt

omit [Fact (0 < L)] in
theorem compatibleJet_smooth {g : DerivativeJet} (h : CompatibleJet L g) (k : ℕ) : ContDiff ℝ ∞ (g k) := by
  have hall (m : ℕ) : ∀ k, ContDiff ℝ m (g k) := by
    induction m with
    | zero => intro k; exact contDiff_zero.mpr (g k).continuous
    | succ m ih =>
      intro k
      rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
      refine ⟨fun x => (h.2 k x).differentiableAt,by simp,?_⟩
      have he : deriv (g k) = (g (k+1) : ℝ → ℂ) := funext (fun x => (h.2 k x).deriv)
      rw [he]
      exact ih (k+1)
  exact contDiff_infty.mpr (fun m => hall m k)

theorem range_derivativeJet : range (derivativeJet (L := L)) = {g : DerivativeJet | CompatibleJet L g} := by
  ext g
  constructor
  · rintro ⟨f,rfl⟩
    exact derivativeJet_compatible f
  · intro hg
    let f : SmoothPeriodicTest L := ⟨g 0,compatibleJet_smooth hg 0,hg.1⟩
    refine ⟨f,?_⟩
    have he (k : ℕ) : iteratedDeriv k (f : ℝ → ℂ) = (g k : ℝ → ℂ) := by
      induction k with
      | zero => rfl
      | succ k ih => rw [iteratedDeriv_succ,ih]; exact funext (fun x => (hg.2 k x).deriv)
    funext k
    apply BoundedContinuousFunction.ext
    intro x
    exact congrFun (he k) x

theorem isClosed_range_derivativeJet : IsClosed (range (derivativeJet (L := L))) := by
  rw [range_derivativeJet]
  exact isClosed_compatibleJet

theorem derivativeJet_injective : Function.Injective (derivativeJet (L := L)) := by
  intro f g h
  apply ext
  intro x
  exact congrArg (fun a : DerivativeJet => a 0 x) h

theorem continuous_derivativeJet : Continuous (derivativeJet (L := L)) := by
  apply continuous_pi
  intro k
  apply withSeminorms.continuous_normedSpace_rng (ℝ →ᵇ ℂ) (derivative (Fact.out : 0 < L).ne' k)
  refine ⟨{k},1,?_⟩
  simp only [Finset.sup_singleton,one_smul]
  intro f
  exact derivative_norm_le_cNorm _ f le_rfl

/-- The original smooth-test space is a closed subspace of the complete product of derivative sup-norm spaces. -/
def derivativeJetEquiv : SmoothPeriodicTest L ≃L[ℂ] LinearMap.range (derivativeJet (L := L)) where
  __ := LinearEquiv.ofInjective derivativeJet derivativeJet_injective
  continuous_toFun := continuous_derivativeJet.subtype_mk _
  continuous_invFun := by
    let e := LinearEquiv.ofInjective (derivativeJet (L := L)) derivativeJet_injective
    change Continuous e.symm.toLinearMap
    apply withSeminorms.continuous_of_continuous_comp e.symm.toLinearMap
    intro N
    change Continuous (fun g => cNorm (Fact.out : 0 < L).ne' N (e.symm g))
    have he (g : LinearMap.range (derivativeJet (L := L))) (j : ℕ) :
        derivative (Fact.out : 0 < L).ne' j (e.symm g) = g.val j :=
      congrFun (LinearEquiv.ofInjective_symm_apply derivativeJet g) j
    simp only [cNorm_apply,he]
    exact continuous_finsetSum _ (fun j _ => ((continuous_apply j).comp continuous_subtype_val).norm)

instance : UniformSpace (SmoothPeriodicTest L) := IsTopologicalAddGroup.rightUniformSpace _
instance : IsUniformAddGroup (SmoothPeriodicTest L) := isUniformAddGroup_of_addCommGroup
instance : CompleteSpace (SmoothPeriodicTest L) := by
  have hi : IsEmbedding (derivativeJet (L := L)) :=
    IsEmbedding.subtypeVal.comp derivativeJetEquiv.toHomeomorph.isEmbedding
  have hu := AddMonoidHom.isUniformInducing_of_isInducing hi.isInducing
  exact hu.completeSpace isClosed_range_derivativeJet.isComplete
instance : T2Space (SmoothPeriodicTest L) := derivativeJetEquiv.toHomeomorph.isEmbedding.t2Space
instance : FirstCountableTopology (SmoothPeriodicTest L) := withSeminorms.firstCountableTopology
instance : TopologicalSpace.MetrizableSpace (SmoothPeriodicTest L) := by
  have : (uniformity (SmoothPeriodicTest L)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.metrizableSpace

instance : Module ℝ (SmoothPeriodicTest L) := inferInstanceAs (Module ℝ (smoothPeriodicTestSubmodule L))
instance : IsScalarTower ℝ ℂ (SmoothPeriodicTest L) := inferInstanceAs (IsScalarTower ℝ ℂ (smoothPeriodicTestSubmodule L))
instance : LocallyConvexSpace ℝ (SmoothPeriodicTest L) := withSeminorms.toLocallyConvexSpace

end NLS.Fourier.SmoothPeriodicTest
