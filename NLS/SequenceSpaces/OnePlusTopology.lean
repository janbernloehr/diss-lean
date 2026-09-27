import NLS.SequenceSpaces.OnePlus
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.Hausdorff

/-!
# The projective topology on `ℓ^(1+)`

The topology on `CoeffOnePlus` is the initial topology for all
coordinate-preserving maps into finite `ℓq`, `q > 1`. Thus a map into
`CoeffOnePlus` is continuous exactly when all its Banach-space
projections are continuous. The topology makes the intersection a
Hausdorff topological complex vector space.
-/

noncomputable section
open scoped ENNReal
namespace NLS.CoeffOnePlus

/-- Finite sequence exponents strictly above one. -/
abbrev Exponent := {q : ℝ≥0∞ // 1 < q ∧ q ≠ ⊤}

/-- The initial topology of the projections to every finite `ℓq`
above one. -/
@[instance_reducible] def projectiveTopology : TopologicalSpace CoeffOnePlus :=
  ⨅ e : Exponent,
    letI : Fact (1 ≤ e.1) := ⟨e.2.1.le⟩
    TopologicalSpace.induced (toCoeffLinear e.1 e.2.1 e.2.2) inferInstance

instance : TopologicalSpace CoeffOnePlus := projectiveTopology

/-- The canonical projections are continuous in the projective
topology. -/
theorem continuous_toCoeff (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hq1 : 1 < q) (hq : q ≠ ⊤) :
    Continuous (toCoeff q hq1 hq) := by
  let e : Exponent := ⟨q,hq1,hq⟩
  apply continuous_iff_le_induced.mpr
  change projectiveTopology ≤ _
  exact iInf_le _ e

/-- Continuity into `ℓ^(1+)` is equivalent to continuity of every
finite-exponent Banach-space projection. -/
theorem continuous_iff_projections {X : Type*} [TopologicalSpace X]
    (f : X → CoeffOnePlus) :
    Continuous f ↔ ∀ e : Exponent,
      letI : Fact (1 ≤ e.1) := ⟨e.2.1.le⟩
      Continuous (fun x => toCoeff e.1 e.2.1 e.2.2 (f x)) := by
  simp only [continuous_iInf_rng, continuous_induced_rng, Function.comp_def]
  rfl

/-- Continuity on a source set is also detected by all the
finite-exponent projections. -/
theorem continuousOn_iff_projections {X : Type*} [TopologicalSpace X]
    (f : X → CoeffOnePlus) (s : Set X) :
    ContinuousOn f s ↔ ∀ e : Exponent,
      letI : Fact (1 ≤ e.1) := ⟨e.2.1.le⟩
      ContinuousOn (fun x => toCoeff e.1 e.2.1 e.2.2 (f x)) s := by
  rw [continuousOn_iff_continuous_domRestrict,
    continuous_iff_projections]
  simp only [continuousOn_iff_continuous_domRestrict]
  rfl

/-- Addition and negation are continuous in the projective topology. -/
instance : IsTopologicalAddGroup CoeffOnePlus := by
  change @IsTopologicalAddGroup CoeffOnePlus projectiveTopology _
  unfold projectiveTopology
  apply topologicalAddGroup_iInf
  intro e
  let : Fact (1 ≤ e.1) := ⟨e.2.1.le⟩
  exact topologicalAddGroup_induced (toCoeffLinear e.1 e.2.1 e.2.2)

/-- The canonical uniform structure of the projective topological
additive group. -/
instance : UniformSpace CoeffOnePlus :=
  IsTopologicalAddGroup.rightUniformSpace CoeffOnePlus

instance : IsUniformAddGroup CoeffOnePlus :=
  isUniformAddGroup_of_addCommGroup

/-- Scalar multiplication is continuous in the projective topology. -/
instance : ContinuousSMul ℂ CoeffOnePlus := by
  change @ContinuousSMul ℂ CoeffOnePlus _ _ projectiveTopology
  unfold projectiveTopology
  apply continuousSMul_iInf
  intro e
  let : Fact (1 ≤ e.1) := ⟨e.2.1.le⟩
  exact continuousSMul_induced (toCoeffLinear e.1 e.2.1 e.2.2)

/-- One projection, for example to `ℓ²`, separates points, so the
projective topology is Hausdorff. -/
instance : T2Space CoeffOnePlus := by
  let e : Exponent := ⟨2,by norm_num,by norm_num⟩
  let : Fact (1 ≤ e.1) := ⟨e.2.1.le⟩
  have hc : Continuous (toCoeff e.1 e.2.1 e.2.2) :=
    continuous_toCoeff e.1 e.2.1 e.2.2
  have hi : Function.Injective (toCoeff e.1 e.2.1 e.2.2) := by
    intro a b hab
    apply Subtype.ext
    funext n
    exact congrArg (fun c : Coeff e.1 => c n) hab
  exact T2Space.of_injective_continuous hi hc

end NLS.CoeffOnePlus
