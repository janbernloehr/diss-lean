import NLS.SequenceSpaces.OnePlusTopology
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.Algebra.IsUniformGroup.Defs

/-!
# Completeness of the projective `ℓ^(1+)` space

The canonical map into the product of the Banach spaces `ℓq`, for
finite `q > 1`, is a uniform embedding. Its image consists exactly
of families whose integer coordinates agree across exponents. These
equalities cut out a closed subset of a complete product, proving
that the projective `ℓ^(1+)` space is complete.
-/

noncomputable section
open Set Metric Topology
open scoped ENNReal
namespace NLS.CoeffOnePlus

/-- The product of all finite Banach sequence exponents above one. -/
abbrev Product := ∀ e : Exponent, Coeff e.1

/-- Send an `ℓ^(1+)` sequence to its family of Banach-space
realizations. -/
def toProduct : CoeffOnePlus →+ Product where
  toFun a e := toCoeff e.1 e.2.1 e.2.2 a
  map_zero' := by
    ext e n
    rfl
  map_add' := by
    intro a b
    ext e n
    rfl

@[simp] theorem toProduct_apply (a : CoeffOnePlus) (e : Exponent)
    (n : ℤ) : toProduct a e n = a.1 n := rfl

/-- The product map is injective because any one exponent retains
all integer coordinates. -/
theorem toProduct_injective : Function.Injective toProduct := by
  intro a b hab
  apply Subtype.ext
  funext n
  let e : Exponent := ⟨2,by norm_num,by norm_num⟩
  exact congrArg (fun x : Product => x e n) hab

/-- The projective topology is the topology induced from the full
product of its Banach-space projections. -/
theorem toProduct_isInducing : IsInducing toProduct := by
  refine ⟨?_⟩
  change projectiveTopology = TopologicalSpace.induced toProduct inferInstance
  rw [induced_to_pi]
  rfl

/-- The product realization is a uniform embedding of additive
groups. -/
theorem toProduct_isUniformEmbedding : IsUniformEmbedding toProduct := by
  have hemb : IsEmbedding toProduct :=
    ⟨toProduct_isInducing,toProduct_injective⟩
  exact AddMonoidHom.isUniformEmbedding_of_isEmbedding hemb

/-- A product family is compatible when all of its integer
coordinates are independent of the Banach exponent. -/
def Compatible (x : Product) : Prop :=
  ∀ (e f : Exponent) (n : ℤ), x e n = x f n

/-- A product family is in the image of `CoeffOnePlus` precisely
when its coordinates agree across exponents. -/
theorem range_toProduct : Set.range toProduct = {x : Product | Compatible x} := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    intro e f n
    rfl
  · intro hx
    let e₀ : Exponent := ⟨2,by norm_num,by norm_num⟩
    have hmem (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤) :
        Memℓp (fun n => x e₀ n) q := by
      let e : Exponent := ⟨q,hq1,hq⟩
      have heq : (fun n => x e₀ n) = fun n => x e n := by
        funext n
        exact hx e₀ e n
      rw [heq]
      exact lp.memℓp (x e)
    let a : CoeffOnePlus := ⟨fun n => x e₀ n,hmem⟩
    refine ⟨a,?_⟩
    funext e
    ext n
    exact hx e₀ e n

/-- Evaluation of one coordinate of an `ℓq` sequence is
continuous. -/
private theorem continuous_eval (e : Exponent) (n : ℤ) :
    Continuous (fun a : Coeff e.1 => a n) := by
  have hq0 : 0 < e.1 := (zero_lt_one.trans e.2.1)
  have hLip : LipschitzWith 1 (fun a : Coeff e.1 => a n) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      have hsub : (a-b) n = a n - b n := rfl
      simpa [dist_eq_norm,hsub] using
        lp.norm_apply_le_norm hq0.ne' (a-b) n
  exact hLip.continuous

/-- Compatibility is a closed condition in the product topology. -/
theorem isClosed_compatible : IsClosed {x : Product | Compatible x} := by
  have hset : {x : Product | Compatible x} =
      ⋂ e : Exponent, ⋂ f : Exponent, ⋂ n : ℤ,
        {x : Product | x e n = x f n} := by
    ext x
    simp [Compatible]
  rw [hset]
  apply isClosed_iInter
  intro e
  apply isClosed_iInter
  intro f
  apply isClosed_iInter
  intro n
  exact isClosed_eq
    ((continuous_eval e n).comp (continuous_apply e))
    ((continuous_eval f n).comp (continuous_apply f))

/-- The projective `ℓ^(1+)` space is complete. -/
instance : CompleteSpace CoeffOnePlus := by
  have hclosed : IsClosed (Set.range toProduct) := by
    rw [range_toProduct]
    exact isClosed_compatible
  exact toProduct_isUniformEmbedding.isUniformInducing.completeSpace
    hclosed.isComplete

end NLS.CoeffOnePlus
