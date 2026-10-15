import NLS.Fourier.PeriodicDistributionPhysicalOrderZero
import NLS.SequenceSpaces.Reflexivity
import NLS.SequenceSpaces.InfinityTruncation
/-! # Fourier–Lebesgue spaces on the original periodic distributions

The carrier consists of original smooth-test functionals whose normalized Fourier
coefficients lie in the stated weighted sequence space. The coefficient norm,
rather than the inherited dual topology, makes this a Banach space. All positive
periods and all real Sobolev orders are included. Reflexivity holds for 1 < p < ∞;
at infinity, norm convergence of Fourier sums is equivalent to the weighted c₀
condition, with an explicit unit-norm counterexample otherwise.
-/
noncomputable section
open scoped ENNReal SchwartzMap
open Filter Topology
namespace NLS.Weight
/-- The source's order-zero Sobolev weight is exactly the unit weight. -/
theorem sobolev_zero_eq_one : sobolev 0 = one := by
  simp [sobolev,one]
end NLS.Weight

namespace NLS.Fourier
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

def periodicFourierLebesgueSubmodule (w : Weight) (p : ℝ≥0∞) : Submodule ℂ (Distribution L) where
  carrier := {u | Memℓp (fun n => (w n : ℂ) * u (mode (-n))) p}
  zero_mem' := by
    change Memℓp (fun n : ℤ => (w n : ℂ) * 0) p
    convert (zero_memℓp (E := fun _ : ℤ => ℂ) (p := p)) using 1
    funext n
    exact mul_zero _
  add_mem' := by
    intro a b ha hb
    change Memℓp (fun n => (w n : ℂ) * (a (mode (-n)) + b (mode (-n)))) p
    change Memℓp (fun n => (w n : ℂ) * a (mode (-n))) p at ha
    change Memℓp (fun n => (w n : ℂ) * b (mode (-n))) p at hb
    convert ha.add hb using 1
    funext n
    exact mul_add _ _ _
  smul_mem' := by
    intro c a ha
    change Memℓp (fun n => (w n : ℂ) * (c * a (mode (-n)))) p
    change Memℓp (fun n => (w n : ℂ) * a (mode (-n))) p at ha
    simpa only [mul_left_comm] using ha.const_mul c

/-- Original distributions with the exact weighted Fourier coefficient norm. -/
def PeriodicFourierLebesgue (L : ℝ) [Fact (0 < L)] (w : Weight) (p : ℝ≥0∞) :=
  ↥(periodicFourierLebesgueSubmodule (L := L) w p)

/-- The source's FL^{s,p}(T_L), with weight (1+|n|)^s. -/
abbrev FourierLebesgueSpace (L : ℝ) [Fact (0 < L)] (s : ℝ) (p : ℝ≥0∞) :=
  PeriodicFourierLebesgue L (Weight.sobolev s) p

namespace PeriodicFourierLebesgue
variable (w : Weight) (p : ℝ≥0∞)
instance : AddCommGroup (PeriodicFourierLebesgue L w p) := inferInstanceAs (AddCommGroup ↥(periodicFourierLebesgueSubmodule (L := L) w p))
instance : Module ℂ (PeriodicFourierLebesgue L w p) := inferInstanceAs (Module ℂ ↥(periodicFourierLebesgueSubmodule (L := L) w p))

def coefficientsLM : PeriodicFourierLebesgue L w p →ₗ[ℂ] WeightedCoeff w p where
  toFun u := ⟨fun n => u.val (mode (-n)),u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefficientsLM_injective : Function.Injective (coefficientsLM (L := L) w p) := by
  intro u v h
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  exact congrArg (fun a : WeightedCoeff w p => a.val n) h

variable [Fact (1 ≤ p)]
instance : NormedAddCommGroup (PeriodicFourierLebesgue L w p) :=
  NormedAddCommGroup.induced _ _ (coefficientsLM w p) (coefficientsLM_injective w p)
instance : NormedSpace ℂ (PeriodicFourierLebesgue L w p) := NormedSpace.induced ℂ _ _ (coefficientsLM w p)

theorem coefficientsLM_surjective (hw : w.HasTemperedInverse) :
    Function.Surjective (coefficientsLM (L := L) w p) := by
  intro a
  let T := arbitraryPeriodDistributionSynthesis L Fact.out w hw a
  have hT : IsPeriodicDistribution L T := arbitraryPeriodDistributionSynthesis_periodic L Fact.out w hw a
  let u : Distribution L := Distribution.ofTempered T
  have hc (n : ℤ) : u (mode (-n)) = a.val n := by
    rw [Distribution.ofTempered_coefficient T hT]
    exact arbitraryPeriodDistributionSynthesis_coefficient L Fact.out w hw a n
  refine ⟨⟨u,?_⟩,?_⟩
  · change Memℓp (fun n => (w n : ℂ)*u (mode (-n))) p
    simp only [hc]
    exact a.property
  · apply Subtype.ext
    funext n
    exact hc n

def coefficientsEquiv (hw : w.HasTemperedInverse) : PeriodicFourierLebesgue L w p ≃ₗ[ℂ] WeightedCoeff w p :=
  LinearEquiv.ofBijective (coefficientsLM w p) ⟨coefficientsLM_injective w p,coefficientsLM_surjective w p hw⟩

def coefficientsIsometry (hw : w.HasTemperedInverse) : PeriodicFourierLebesgue L w p ≃ₗᵢ[ℂ] WeightedCoeff w p where
  toLinearEquiv := coefficientsEquiv w p hw
  norm_map' _ := rfl

theorem completeSpace (hw : w.HasTemperedInverse) : CompleteSpace (PeriodicFourierLebesgue L w p) :=
  (coefficientsIsometry w p hw).toIsometryEquiv.completeSpace

def truncate (hw : w.HasTemperedInverse) (S : Finset ℤ) (u : PeriodicFourierLebesgue L w p) : PeriodicFourierLebesgue L w p :=
  (coefficientsEquiv w p hw).symm (WeightedCoeff.truncate w p S (coefficientsLM w p u))

theorem truncate_coefficient (hw : w.HasTemperedInverse) (S : Finset ℤ) (u : PeriodicFourierLebesgue L w p) (n : ℤ) :
    (truncate w p hw S u).val (mode (-n)) = if n ∈ S then u.val (mode (-n)) else 0 := by
  change (coefficientsEquiv w p hw (truncate w p hw S u)).val n = _
  rw [truncate,LinearEquiv.apply_symm_apply]
  exact WeightedCoeff.truncate_apply w p S (coefficientsLM w p u) n

theorem tendsto_truncate (hw : w.HasTemperedInverse) (hp : p ≠ ⊤) (u : PeriodicFourierLebesgue L w p) :
    Tendsto (fun S : Finset ℤ => truncate w p hw S u) atTop (𝓝 u) := by
  have h := ((coefficientsIsometry (L := L) w p hw).symm.continuous.tendsto (coefficientsLM w p u)).comp
    (WeightedCoeff.tendsto_truncate w p hp (coefficientsLM w p u))
  change Tendsto (fun S => truncate w p hw S u) atTop (𝓝 ((coefficientsEquiv w p hw).symm (coefficientsEquiv w p hw u))) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

theorem tendsto_truncate_top_iff (hw : w.HasTemperedInverse) (u : PeriodicFourierLebesgue L w ⊤) :
    Tendsto (fun S : Finset ℤ => truncate w ⊤ hw S u) atTop (𝓝 u) ↔
      ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℤ, ∀ n ∉ S, ‖(w n : ℂ)*u.val (mode (-n))‖ ≤ ε := by
  have he : Tendsto (fun S : Finset ℤ => truncate w ⊤ hw S u) atTop (𝓝 u) ↔
      Tendsto (fun S : Finset ℤ => WeightedCoeff.truncate w ⊤ S (coefficientsLM w ⊤ u))
        atTop (𝓝 (coefficientsLM w ⊤ u)) := by
    constructor
    · intro h
      have ht := ((coefficientsIsometry (L := L) w ⊤ hw).continuous.tendsto u).comp h
      change Tendsto (fun S => coefficientsEquiv w ⊤ hw (truncate w ⊤ hw S u)) atTop (𝓝 (coefficientsLM w ⊤ u)) at ht
      simpa only [truncate,LinearEquiv.apply_symm_apply] using ht
    · intro h
      have ht := ((coefficientsIsometry (L := L) w ⊤ hw).symm.continuous.tendsto (coefficientsLM w ⊤ u)).comp h
      change Tendsto (fun S => truncate w ⊤ hw S u) atTop (𝓝 ((coefficientsEquiv w ⊤ hw).symm (coefficientsEquiv w ⊤ hw u))) at ht
      simpa only [LinearEquiv.symm_apply_apply] using ht
  exact he.trans (WeightedCoeff.tendsto_truncate_top_iff w (coefficientsLM w ⊤ u))

theorem bidual_surjective (hw : w.HasTemperedInverse) (hp : 1 < p) (hpf : p ≠ ⊤) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ (PeriodicFourierLebesgue L w p)) := by
  intro F
  let e := (coefficientsIsometry (L := L) w p hw).toContinuousLinearEquiv
  let F' := F.comp (e.toContinuousLinearMap.precomp ℂ)
  obtain ⟨x,hx⟩ := WeightedCoeff.bidual_surjective w hp hpf F'
  refine ⟨e.symm x,?_⟩
  apply ContinuousLinearMap.ext
  intro K
  have h := congrArg (fun G : (WeightedCoeff w p →L[ℂ] ℂ) →L[ℂ] ℂ => G (K.comp e.symm.toContinuousLinearMap)) hx
  change K (e.symm x) = F K
  change K (e.symm x) = F ((K.comp e.symm.toContinuousLinearMap).comp e.toContinuousLinearMap) at h
  convert h using 1
  congr 1
  ext z
  simp [e]


theorem norm_eq (u : PeriodicFourierLebesgue L w p) :
    ‖u‖ = ‖WeightedCoeff.weightEquiv w p (coefficientsLM w p u)‖ := rfl

instance sobolev_complete (s : ℝ) : CompleteSpace (PeriodicFourierLebesgue L (Weight.sobolev s) p) :=
  completeSpace _ _ (Weight.hasTemperedInverse_sobolev s)

instance unweighted_complete : CompleteSpace (PeriodicFourierLebesgue L Weight.one p) :=
  completeSpace _ _ Weight.hasTemperedInverse_one

def inverseWeightDistribution (hw : w.HasTemperedInverse) : PeriodicFourierLebesgue L w ⊤ :=
  (coefficientsEquiv w ⊤ hw).symm (WeightedCoeff.inverseWeightCoefficients w)

theorem inverseWeightDistribution_coefficient (hw : w.HasTemperedInverse) (n : ℤ) :
    (inverseWeightDistribution (L := L) w hw).val (mode (-n)) = (w n : ℂ)⁻¹ := by
  change (coefficientsEquiv w ⊤ hw (inverseWeightDistribution w hw)).val n = _
  rw [inverseWeightDistribution,LinearEquiv.apply_symm_apply]
  exact WeightedCoeff.inverseWeightCoefficients_val w n

theorem norm_inverseWeightDistribution (hw : w.HasTemperedInverse) :
    ‖inverseWeightDistribution (L := L) w hw‖ = 1 := by
  change ‖(coefficientsIsometry (L := L) w ⊤ hw).symm (WeightedCoeff.inverseWeightCoefficients w)‖ = 1
  rw [LinearIsometryEquiv.norm_map,WeightedCoeff.norm_inverseWeightCoefficients]

theorem norm_inverseWeightDistribution_sub_truncate (hw : w.HasTemperedInverse) (S : Finset ℤ) :
    ‖inverseWeightDistribution (L := L) w hw-truncate w ⊤ hw S (inverseWeightDistribution w hw)‖ = 1 := by
  rw [← (coefficientsIsometry (L := L) w ⊤ hw).norm_map]
  change ‖coefficientsEquiv w ⊤ hw (inverseWeightDistribution w hw - truncate w ⊤ hw S (inverseWeightDistribution w hw))‖ = 1
  rw [map_sub,truncate,LinearEquiv.apply_symm_apply,inverseWeightDistribution,LinearEquiv.apply_symm_apply]
  change ‖WeightedCoeff.inverseWeightCoefficients w - WeightedCoeff.truncate w ⊤ S
    (coefficientsEquiv w ⊤ hw ((coefficientsEquiv w ⊤ hw).symm (WeightedCoeff.inverseWeightCoefficients w)))‖ = 1
  rw [LinearEquiv.apply_symm_apply]
  exact WeightedCoeff.norm_inverseWeightCoefficients_sub_truncate w S

theorem not_tendsto_truncate_inverseWeightDistribution (hw : w.HasTemperedInverse) :
    ¬Tendsto (fun S : Finset ℤ => truncate w ⊤ hw S (inverseWeightDistribution (L := L) w hw))
      atTop (𝓝 (inverseWeightDistribution w hw)) := by
  intro h
  obtain ⟨S,hS⟩ := (tendsto_truncate_top_iff w hw _).mp h (1/2) (by norm_num)
  obtain ⟨n,hn⟩ := S.exists_notMem
  have hb := hS n hn
  rw [inverseWeightDistribution_coefficient,mul_inv_cancel₀ (w.complex_ne_zero n)] at hb
  norm_num at hb
/-- At unit weight the endpoint obstruction is the actual point evaluation at zero. -/
theorem inverseWeightDistribution_one :
    (inverseWeightDistribution (L := L) Weight.one Weight.hasTemperedInverse_one).val = Distribution.evaluation 0 := by
  apply Distribution.ext_coefficients
  intro n
  simp only [inverseWeightDistribution_coefficient,Weight.one_apply,Complex.ofReal_one,inv_one,
    Distribution.evaluation_zero_coefficient]

end PeriodicFourierLebesgue
end NLS.Fourier
