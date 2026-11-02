import NLS.SequenceSpaces.GlobalScalarActionFamilyDescent
import NLS.SequenceSpaces.WeightedNonnegativeActions

/-! # Common action descent in the original weighted norm

The weighted action map retains raw coefficients. In normalized Hilbert
coordinates its n-th raw action is (x_n²+y_n²)/(2*w_n). The complete
weighted nonnegative cone and the raw-coordinate quadratic tail bounds
are transported through the weighting isometry without changing scale.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal Classical
namespace NLS.WeightedCoeff

/-- Quadratic actions of normalized Hilbert coordinates, with their raw
values in the original weighted action space. -/
def actionsFromNormalizedCoordinates (w : Weight) (z : Coeff 2 × Coeff 2) : WeightedCoeff w 1 :=
  (weightIsometry w 1).symm (quadraticActionsExponent (q := 1) z)

@[simp] theorem weight_actionsFromNormalizedCoordinates (w : Weight) (z : Coeff 2 × Coeff 2) :
    weightIsometry w 1 (actionsFromNormalizedCoordinates w z) =
      quadraticActionsExponent (q := 1) z :=
  (weightIsometry w 1).apply_symm_apply _

/-- The positive weight is divided out exactly once. -/
theorem actionsFromNormalizedCoordinates_apply (w : Weight) (z : Coeff 2 × Coeff 2) (k : ℤ) :
    (actionsFromNormalizedCoordinates w z).val k = (z.1 k^2+z.2 k^2)/(2*(w k : ℂ)) := by
  change quadraticActionsExponent (q := 1) z k/(w k : ℂ) = _
  rw [quadraticActionsExponent_apply,div_div]

/-- Weighting preserves equality of the original raw action sequences. -/
theorem actionsFromNormalizedCoordinates_eq_iff (w : Weight) (z v : Coeff 2 × Coeff 2) :
    actionsFromNormalizedCoordinates w z = actionsFromNormalizedCoordinates w v ↔
      quadraticActionsExponent (q := 1) z = quadraticActionsExponent v :=
  (weightIsometry w 1).symm.injective.eq_iff

/-- Transport a scalar action family through a continuous linear
coordinate equivalence, preserving its local tail bounds. The abstract
source and action spaces keep this proof independent of weight instances. -/
theorem transport_scalar_action_family_with_tail_bounds
    {ι X E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : F ≃L[ℂ] E) (S : Set F) (S₀ : Set E)
    (hS : ∀ b ∈ S, L b ∈ S₀) (A : Set X)
    (I : X → F) (I₀ : X → E) (hI : ∀ x, L (I x) = I₀ x)
    (f : ι → X → ℂ) (J : ι → F → ℂ) (J₀ : ι → E → ℂ)
    (hJ : ∀ i b, J₀ i (L b) = J i b)
    (V₀ : Set E) (G₀ : ι → E → ℂ)
    (hV₀ : IsOpen V₀) (hcone : S₀ ⊆ V₀)
    (hG₀ : ∀ i, AnalyticOnNhd ℂ (G₀ i) V₀)
    (hrec : ∀ i, ∀ x ∈ A, G₀ i (I₀ x) = f i x)
    (hlocal : ∀ b ∈ V₀, ∃ T : Set E, IsOpen T ∧ b ∈ T ∧ T ⊆ V₀ ∧
      ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ T, ∀ i ∉ s,
        ‖G₀ i c‖ ≤ C*‖J₀ i c‖^2) :
    ∃ V : Set F, ∃ G : ι → F → ℂ,
      IsOpen V ∧ S ⊆ V ∧ (∀ i, AnalyticOnNhd ℂ (G i) V) ∧
      (∀ i, ∀ x ∈ A, G i (I x) = f i x) ∧
      ∀ b ∈ V, ∃ T : Set F, IsOpen T ∧ b ∈ T ∧ T ⊆ V ∧
        ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ T, ∀ i ∉ s,
          ‖G i c‖ ≤ C*‖J i c‖^2 := by
  let V := L ⁻¹' V₀
  let G : ι → F → ℂ := fun i b => G₀ i (L b)
  refine ⟨V,G,hV₀.preimage L.continuous,fun b hb => hcone (hS b hb),?_,?_,?_⟩
  · intro i b hb
    exact (hG₀ i (L b) hb).comp (L.analyticAt b)
  · intro i x hx
    change G₀ i (L (I x)) = _
    rw [hI]
    exact hrec i x hx
  · intro b hb
    obtain ⟨T,hT,hbT,hTV,s,C,hC,hbnd⟩ := hlocal (L b) hb
    refine ⟨L ⁻¹' T,hT.preimage L.continuous,hbT,fun c hc => hTV hc,s,C,hC,?_⟩
    intro c hc i hi
    have hh := hbnd (L c) hc i hi
    rw [hJ] at hh
    exact hh

/-- Construct one complex open weighted-action neighborhood of the entire
nonnegative cone, retaining the local quadratic estimates in raw actions. -/
theorem exists_global_scalar_action_family_with_raw_tail_bounds {ι : Type*}
    (w : Weight) (k : ι → ℤ) (f : ι → (Coeff 2 × Coeff 2) → ℂ)
    (U : Set (Coeff 2 × Coeff 2)) (hU : IsOpen U) (hrealU : Coeff.realPairLocus 2 ⊆ U)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (hinv : ∀ i, ∀ z ∈ U, ∀ v ∈ U,
      z ∈ Coeff.realPairLocus 2 → v ∈ Coeff.realPairLocus 2 →
      actionsFromNormalizedCoordinates w v = actionsFromNormalizedCoordinates w z → f i v = f i z)
    (hbound : ∀ z ∈ Coeff.realPairLocus 2,
      ∃ W : Set (Coeff 2 × Coeff 2), IsOpen W ∧ z ∈ W ∧ W ⊆ U ∧
        ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ W, ∀ i ∉ s,
          ‖f i v‖ ≤ C*‖(actionsFromNormalizedCoordinates w v).val (k i)‖^2) :
    ∃ V : Set (WeightedCoeff w 1), ∃ G : ι → WeightedCoeff w 1 → ℂ,
      IsOpen V ∧ nonnegativeLocus w 1 ⊆ V ∧
      (∀ i, AnalyticOnNhd ℂ (G i) V) ∧
      (∀ i, ∀ z ∈ Coeff.realPairLocus 2, G i (actionsFromNormalizedCoordinates w z) = f i z) ∧
      ∀ b ∈ V, ∃ T : Set (WeightedCoeff w 1), IsOpen T ∧ b ∈ T ∧ T ⊆ V ∧
        ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ T, ∀ i ∉ s,
          ‖G i c‖ ≤ C*‖c.val (k i)‖^2 := by
  let L : WeightedCoeff w 1 ≃L[ℂ] Coeff 1 := (weightIsometry w 1).toContinuousLinearEquiv
  let J : ι → Coeff 1 → ℂ := fun i b => (L.symm b).val (k i)
  have hJactions (i : ι) (z : Coeff 2 × Coeff 2) :
      J i (quadraticActionsExponent (q := 1) z) = (actionsFromNormalizedCoordinates w z).val (k i) := rfl
  have hboundJ : ∀ z ∈ Coeff.realPairLocus 2,
      ∃ W : Set (Coeff 2 × Coeff 2), IsOpen W ∧ z ∈ W ∧ W ⊆ U ∧
        ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ W, ∀ i ∉ s,
          ‖f i v‖ ≤ C*‖J i (quadraticActionsExponent (q := 1) v)‖^2 := by
    intro z hz
    obtain ⟨W,hW,hzW,hWU,s,C,hC,hb⟩ := hbound z hz
    refine ⟨W,hW,hzW,hWU,s,C,hC,?_⟩
    intro v hv i hi
    rw [hJactions]
    exact hb v hv i hi
  obtain ⟨V₀,G₀,hV₀,hcone,hG₀,hrec,hlocal⟩ :=
    Coeff.exists_global_scalar_action_family_with_tail_bounds (p := 2) (q := 1)
      (by norm_num) J f U hU hrealU hf
      (fun i z hz v hv hzr hvr he => hinv i z hz v hv hzr hvr
        ((actionsFromNormalizedCoordinates_eq_iff w v z).mpr he)) hboundJ
  apply transport_scalar_action_family_with_tail_bounds L
    (nonnegativeLocus w 1) (Coeff.nonnegativeLocus 1)
    (fun b hb => (mem_nonnegativeLocus_iff w 1 b).mp hb)
    (Coeff.realPairLocus 2) (actionsFromNormalizedCoordinates w)
    (quadraticActionsExponent (p := 2) (q := 1))
    (weight_actionsFromNormalizedCoordinates w) f
    (fun i b => b.val (k i)) J (fun i b => ?_)
    V₀ G₀ hV₀ hcone hG₀ hrec hlocal
  change (L.symm (L b)).val (k i) = b.val (k i)
  rw [L.symm_apply_apply]

end NLS.WeightedCoeff
