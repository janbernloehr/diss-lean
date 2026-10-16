import NLS.Fourier.PeriodicFourierLebesgueEndpoints
import NLS.Fourier.RudinShapiro
import NLS.SequenceSpaces.YoungConvolution

/-!
# Lemma A.7: products on the original Fourier–Lebesgue spaces

For every positive physical period and every Banach Young triple, coefficient
convolution defines a unique original periodic distribution. Its bilinear
operator norm is exactly one. The product is independent of the exponents
used to represent its factors and agrees with pointwise multiplication when
one factor has an absolutely convergent Fourier series and both are continuous.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace NLS.Fourier
open SmoothPeriodicTest
namespace PeriodicFourierLebesgue
variable {L : ℝ} [Fact (0 < L)]
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- The original-distribution product defined by absolutely convergent coefficient convolution. -/
def youngProduct (h : YoungRelation p q r)
    (u : PeriodicFourierLebesgue L Weight.one p) (v : PeriodicFourierLebesgue L Weight.one q) :
    PeriodicFourierLebesgue L Weight.one r :=
  (unweightedCoefficients r).symm
    (Coeff.youngConvolution h (unweightedCoefficients p u) (unweightedCoefficients q v))

/-- The normalized Fourier coefficient of the product is the convolution coefficient. -/
theorem youngProduct_coefficient (h : YoungRelation p q r)
    (u : PeriodicFourierLebesgue L Weight.one p) (v : PeriodicFourierLebesgue L Weight.one q) (n : ℤ) :
    (youngProduct h u v).val (mode (-n)) = ∑' k : ℤ, u.val (mode (-(n-k))) * v.val (mode (-k)) := by
  rw [← unweightedCoefficients_apply,youngProduct,LinearIsometryEquiv.apply_symm_apply]
  simp only [Coeff.youngConvolution_apply,unweightedCoefficients_apply]

omit [Fact (1 ≤ r)] in
/-- Every convolution coefficient is absolutely summable, including the infinity endpoints. -/
theorem summable_norm_youngProduct_terms (h : YoungRelation p q r)
    (u : PeriodicFourierLebesgue L Weight.one p) (v : PeriodicFourierLebesgue L Weight.one q) (n : ℤ) :
    Summable (fun k : ℤ => ‖u.val (mode (-(n-k))) * v.val (mode (-k))‖) := by
  simpa only [unweightedCoefficients_apply] using
    Coeff.summable_norm_youngConvolution_terms h (unweightedCoefficients p u) (unweightedCoefficients q v) n

/-- Lemma A.7 with its exact constant one. -/
theorem norm_youngProduct_le (h : YoungRelation p q r)
    (u : PeriodicFourierLebesgue L Weight.one p) (v : PeriodicFourierLebesgue L Weight.one q) :
    ‖youngProduct h u v‖ ≤ ‖u‖ * ‖v‖ := by
  simpa only [youngProduct,LinearIsometryEquiv.norm_map] using
    Coeff.norm_youngConvolution_le h (unweightedCoefficients p u) (unweightedCoefficients q v)

/-- The product is additive in its first argument. -/
theorem youngProduct_add_left (h : YoungRelation p q r)
    (u u' : PeriodicFourierLebesgue L Weight.one p) (v : PeriodicFourierLebesgue L Weight.one q) :
    youngProduct h (u+u') v = youngProduct h u v + youngProduct h u' v := by
  simp only [youngProduct,map_add,Coeff.youngConvolution_add_left]

/-- The product is additive in its second argument. -/
theorem youngProduct_add_right (h : YoungRelation p q r)
    (u : PeriodicFourierLebesgue L Weight.one p) (v v' : PeriodicFourierLebesgue L Weight.one q) :
    youngProduct h u (v+v') = youngProduct h u v + youngProduct h u v' := by
  simp only [youngProduct,map_add,Coeff.youngConvolution_add_right]

/-- Complex scalars commute with the first product argument. -/
theorem youngProduct_smul_left (h : YoungRelation p q r) (c : ℂ)
    (u : PeriodicFourierLebesgue L Weight.one p) (v : PeriodicFourierLebesgue L Weight.one q) :
    youngProduct h (c • u) v = c • youngProduct h u v := by
  simp only [youngProduct,map_smul,Coeff.youngConvolution_smul_left]

/-- Complex scalars commute with the second product argument. -/
theorem youngProduct_smul_right (h : YoungRelation p q r) (c : ℂ)
    (u : PeriodicFourierLebesgue L Weight.one p) (v : PeriodicFourierLebesgue L Weight.one q) :
    youngProduct h u (c • v) = c • youngProduct h u v := by
  simp only [youngProduct,map_smul,Coeff.youngConvolution_smul_right]

/-- The continuous complex-bilinear product on the original spaces. -/
def youngProductCLM (h : YoungRelation p q r) :
    PeriodicFourierLebesgue L Weight.one p →L[ℂ]
      PeriodicFourierLebesgue L Weight.one q →L[ℂ] PeriodicFourierLebesgue L Weight.one r :=
  (LinearMap.mk₂ ℂ (youngProduct h) (youngProduct_add_left h) (youngProduct_smul_left h)
    (youngProduct_add_right h) (youngProduct_smul_right h)).mkContinuous₂ 1
    (fun u v => by simpa only [one_mul,LinearMap.mk₂_apply] using norm_youngProduct_le h u v)

/-- The bilinear map evaluates to the coefficient-defined product. -/
theorem youngProductCLM_apply (h : YoungRelation p q r)
    (u : PeriodicFourierLebesgue L Weight.one p) (v : PeriodicFourierLebesgue L Weight.one q) :
    youngProductCLM h u v = youngProduct h u v := rfl

/-- The bilinear operator norm is at most one. -/
theorem norm_youngProductCLM_le (h : YoungRelation p q r) : ‖youngProductCLM (L := L) h‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- Swapping the factors swaps the input exponents and preserves the product. -/
theorem youngProduct_comm (h : YoungRelation p q r)
    (u : PeriodicFourierLebesgue L Weight.one p) (v : PeriodicFourierLebesgue L Weight.one q) :
    youngProduct h u v = youngProduct h.symm v u := by
  unfold youngProduct
  rw [Coeff.youngConvolution_comm]

/-- The convolution coefficients determine the product among all original distributions. -/
theorem youngProduct_unique (h : YoungRelation p q r)
    (u : PeriodicFourierLebesgue L Weight.one p) (v : PeriodicFourierLebesgue L Weight.one q)
    (w : Distribution L)
    (hw : ∀ n, w (mode (-n)) = ∑' k : ℤ, u.val (mode (-(n-k))) * v.val (mode (-k))) :
    (youngProduct h u v).val = w := by
  apply Distribution.ext_coefficients
  intro n
  rw [youngProduct_coefficient,hw]

/-- The underlying product does not depend on the exponents representing its factors. -/
theorem youngProduct_eq_of_val_eq
    {p' q' r' : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ q')] [Fact (1 ≤ r')]
    (h : YoungRelation p q r) (h' : YoungRelation p' q' r')
    (u : PeriodicFourierLebesgue L Weight.one p) (v : PeriodicFourierLebesgue L Weight.one q)
    (u' : PeriodicFourierLebesgue L Weight.one p') (v' : PeriodicFourierLebesgue L Weight.one q')
    (hu : u.val = u'.val) (hv : v.val = v'.val) :
    (youngProduct h u v).val = (youngProduct h' u' v').val := by
  apply Distribution.ext_coefficients
  intro n
  simp only [youngProduct_coefficient,hu,hv]

/-- Joint continuity in both original-space norms. -/
theorem continuous_youngProduct (h : YoungRelation p q r) :
    Continuous (fun uv : PeriodicFourierLebesgue L Weight.one p × PeriodicFourierLebesgue L Weight.one q =>
      youngProduct h uv.1 uv.2) :=
  (((youngProductCLM h).continuous.comp continuous_fst).clm_apply continuous_snd)

/-- Simultaneous finite Fourier truncations converge to the product for finite input exponents. -/
theorem tendsto_youngProduct_truncate (h : YoungRelation p q r) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (u : PeriodicFourierLebesgue L Weight.one p) (v : PeriodicFourierLebesgue L Weight.one q) :
    Tendsto (fun S : Finset ℤ => youngProduct h (truncate Weight.one p Weight.hasTemperedInverse_one S u)
      (truncate Weight.one q Weight.hasTemperedInverse_one S v)) atTop (𝓝 (youngProduct h u v)) :=
  by
  have hu := tendsto_truncate Weight.one p Weight.hasTemperedInverse_one hp u
  have hv := tendsto_truncate Weight.one q Weight.hasTemperedInverse_one hq v
  have hpair : Tendsto (fun S : Finset ℤ =>
      (truncate Weight.one p Weight.hasTemperedInverse_one S u,
       truncate Weight.one q Weight.hasTemperedInverse_one S v)) atTop (𝓝 (u,v)) := hu.prodMk_nhds hv
  simpa only [Function.comp_def] using! ((continuous_youngProduct (L := L) h).tendsto (u,v)).comp hpair

/-- The constant one in A.7 is sharp for every Banach Young triple. -/
theorem norm_youngProductCLM (h : YoungRelation p q r) : ‖youngProductCLM (L := L) h‖ = 1 := by
  apply le_antisymm (norm_youngProductCLM_le h)
  rw [← Coeff.norm_youngConvolutionCLM h]
  apply ContinuousLinearMap.opNorm_le_bound (Coeff.youngConvolutionCLM h) (norm_nonneg (youngProductCLM (L := L) h))
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro b
  have hh := (youngProductCLM (L := L) h).le_opNorm₂
    ((unweightedCoefficients p).symm a) ((unweightedCoefficients q).symm b)
  simpa only [youngProductCLM_apply,youngProduct,LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.norm_map,Coeff.youngConvolutionCLM_apply] using hh

/-- Actual continuous multiplication by a Wiener representative has convolution coefficients. -/
theorem fourierCoeff_mul_continuousRepresentative (f : C(AddCircle L,ℂ))
    (v : PeriodicFourierLebesgue L Weight.one 1) (n : ℤ) :
    fourierCoeff (f * continuousRepresentative v : C(AddCircle L,ℂ)) n =
      ∑' k : ℤ, fourierCoeff f (n-k) * v.val (mode (-k)) := by
  let F : C(AddCircle L,ℂ) →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp
    (fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousMap.toLp (E := ℂ) 2 (AddCircle.haarAddCircle (T := L)) ℂ))
  have hF (g : C(AddCircle L,ℂ)) : F g = fourierCoeff g n :=
    (fourierBasis_repr _ n).trans (fourierCoeff_toLp g n)
  let G : C(AddCircle L,ℂ) →L[ℂ] ℂ := F.comp (ContinuousLinearMap.mul ℂ C(AddCircle L,ℂ) f)
  have hG (g : C(AddCircle L,ℂ)) : G g = fourierCoeff (f*g : C(AddCircle L,ℂ)) n := hF _
  have h := (G.hasSum (hasSum_continuousRepresentative v)).tsum_eq.symm
  rw [hG] at h
  rw [h]
  apply tsum_congr
  intro k
  rw [hG,mul_smul_comm,mul_comm f (fourier k)]
  rw [ContinuousMap.coe_smul,fourierCoeff.const_smul,fourierCoeff_fourier_mul]
  exact mul_comm _ _

/-- The original product agrees with pointwise multiplication of continuous representatives. -/
theorem youngProduct_eq_ofContinuous (h : YoungRelation p 1 p)
    (u : PeriodicFourierLebesgue L Weight.one p) (v : PeriodicFourierLebesgue L Weight.one 1)
    (f : C(AddCircle L,ℂ)) (hf : Distribution.ofContinuous f = u.val) :
    (youngProduct h u v).val = Distribution.ofContinuous (f * continuousRepresentative v) := by
  apply Distribution.ext_coefficients
  intro n
  rw [youngProduct_coefficient,Distribution.ofContinuous_coefficient,fourierCoeff_mul_continuousRepresentative]
  apply tsum_congr
  intro k
  rw [← hf,Distribution.ofContinuous_coefficient]

/-- For two Wiener elements, the representative of their product is their pointwise product. -/
theorem continuousRepresentative_youngProduct
    (u v : PeriodicFourierLebesgue L Weight.one 1) :
    continuousRepresentative (youngProduct (show YoungRelation 1 1 1 by simp [YoungRelation]) u v) =
      continuousRepresentative u * continuousRepresentative v := by
  apply Distribution.ofContinuous_injective
  rw [continuousRepresentative_represents]
  exact youngProduct_eq_ofContinuous _ u v _ (continuousRepresentative_represents u)


end PeriodicFourierLebesgue
end NLS.Fourier
