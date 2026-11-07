import NLS.Articles.KdVPseudomeasures.NativeEndpointRealLocalInverse
import NLS.Articles.KdVPseudomeasures.NativeEndpointLocalInverse
import NLS.KdV.PeriodOneEndpointRealSource

/-! Every original real endpoint potential is retained as the SAME
physical distribution, in the exact closed real mean-zero Banach model.
The actual endpoint coordinates, actions and Fourier derivatives use the
original even period-two modes without renormalizing the potential. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

def originalEndpointRealSource (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    HillEndpointRealMeanZeroSource r :=
  ⟨⟨periodOneEndpointExtract r hr.1 q.val,by
      change (periodOneEndpointExtract r hr.1 q.val).val 0=0
      simpa only [periodOneEndpointExtract_apply,mul_zero,neg_zero] using q.property.2.1⟩,
    periodOneEndpointExtract_real r hr.1 q.val q.property.1⟩

theorem originalEndpointRealSource_same_distribution (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    periodOneEndpointOriginal r hr.1 (originalEndpointRealSource r hr q).val.val=q.val :=
  periodOneEndpointOriginal_extract r hr.1 q.val q.property.2.2

def originalEndpointPotential (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointRealMeanZeroSource r) : Potential r :=
  ⟨periodOneEndpointOriginal r hr.1 q.val.val,
    (periodOneEndpointOriginal_source_iff r hr.1 q.val.val).mpr ⟨q.property,q.val.property⟩⟩

def originalEndpointRealSourceEquiv (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Potential r ≃ HillEndpointRealMeanZeroSource r where
  toFun := originalEndpointRealSource r hr
  invFun := originalEndpointPotential r hr
  left_inv q := by
    apply Subtype.ext
    exact originalEndpointRealSource_same_distribution r hr q
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    exact periodOneEndpointExtract_original r hr.1 q.val.val

theorem norm_originalEndpointRealSource_le (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    ‖originalEndpointRealSource r hr q‖ ≤ (2:ℝ)^r*‖q.val‖ :=
  norm_periodOneEndpointExtract_le r hr.1 q.val

theorem norm_originalEndpointPotential_le (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointRealMeanZeroSource r) : ‖(originalEndpointPotential r hr q).val‖ ≤ ‖q‖ :=
  norm_periodOneEndpointOriginal_le r hr.1 q.val.val

theorem originalEndpointRealSource_native (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    endpointNativeInclusion r hr (originalEndpointRealSource r hr q).val.val=sourceNativePeriodOneCLM r hr q.val := by
  have h := sourceNativePeriodOneCLM_endpointOriginal r hr (originalEndpointRealSource r hr q).val.val
  rw [originalEndpointRealSource_same_distribution] at h
  exact h.symm

def originalEndpointRealSignedCoordinates (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    HillEndpointRealSignedTarget r :=
  hillEndpointRealSignedMap r hr (originalEndpointRealSource r hr q)

theorem original_endpoint_real_coordinate_matches_native (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (k : ℤ) :
    (originalEndpointRealSignedCoordinates r hr q).val.val.val k=
      (hillHminusNativeComplexMap (sourceNativePeriodOneCLM r hr q.val)).val k := by
  rw [originalEndpointRealSignedCoordinates,hillEndpointRealSignedMap_coe,
    hillEndpointMeanZeroMap_real_coordinate r hr _ (endpointNativeInclusion_real_source r hr _),
    originalEndpointRealSource_native]

theorem original_endpoint_real_action (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (n : ℕ+) :
    (originalEndpointRealSignedCoordinates r hr q).val.val.val (n:ℤ)*
      (originalEndpointRealSignedCoordinates r hr q).val.val.val (-(n:ℤ))=
        hillHminusCanonicalAction n (sourceNativePeriodOneCLM r hr q.val) := by
  rw [original_endpoint_real_coordinate_matches_native,original_endpoint_real_coordinate_matches_native]
  apply hillHminusNativeComplexMap_action_identity
  rw [← originalEndpointRealSource_native r hr q]
  exact real_mem_hillHminusActionAngleNativeDomain _
    (endpointNativeInclusion_real_source r hr (originalEndpointRealSource r hr q))

theorem original_endpoint_real_derivative_even_modes (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (n : ℕ+) :
    ((fderiv ℝ (hillEndpointRealSignedMap r hr) 0) (originalEndpointRealSource r hr q)).val.val.val (n:ℤ)=
      q.val.val (mode (-(2*(n:ℤ))))/(Real.sqrt (2*Real.pi*(n:ℕ)):ℂ) ∧
    ((fderiv ℝ (hillEndpointRealSignedMap r hr) 0) (originalEndpointRealSource r hr q)).val.val.val (-(n:ℤ))=
      q.val.val (mode (2*(n:ℤ)))/(Real.sqrt (2*Real.pi*(n:ℕ)):ℂ) := by
  rw [fderiv_hillEndpointRealSignedMap_zero_apply,fderiv_hillEndpointRealSignedMap_zero_apply,
    WeightedCoeff.halfFourierSymbol_neg,WeightedCoeff.halfFourierSymbol_positive]
  simp only [originalEndpointRealSource,periodOneEndpointExtract_apply,mul_neg,neg_neg]
  constructor <;> ring

end NLS.Articles.KdVPseudomeasures
