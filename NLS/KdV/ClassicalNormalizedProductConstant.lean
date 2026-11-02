import NLS.KdV.ClassicalNormalizedProductAsymptotics
import NLS.ComplexAnalysis.EntireCircleDecay
import NLS.ZakharovShabat.CentralCircleThresholds

/-! # Constancy and completeness for the actual normalized product

The entire quotient equals the actual analytic residue sum. Simplicity
at one selected zero proves this scalar nonzero and excludes extra Psi_n
zeros. The scalar's exact value at nonzero potentials is still separate.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
/-- Complete actual normalized products with the explicitly retained
leading scalar. The source's claim that this scalar is one is not a field. -/
structure ClassicalNormalizedProductData (N : ℕ)
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n : ℕ+) (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) : Prop where
  leading_ne_zero : classicalHillNormalizedLeadingCoefficient Q n t.2 ≠ 0
  quotient_constant : ∀ lambda : ℂ, classicalHillNormalizedProductQuotient N R n t lambda =
    classicalHillNormalizedLeadingCoefficient Q n t.2
  product_identity : ∀ lambda : ℂ, classicalHillNormalizedNumerator N R n (lambda,t.2) =
    classicalHillNormalizedLeadingCoefficient Q n t.2*classicalHillCandidateOmittedProduct N n t lambda
  product_convergence : TendstoLocallyUniformlyOn
    (fun M lambda => classicalHillNormalizedLeadingCoefficient Q n t.2*
      classicalHillCandidateOmittedPartialProduct N n t lambda M)
    (fun lambda => classicalHillNormalizedNumerator N R n (lambda,t.2)) atTop univ
  zero_iff : ∀ lambda : ℂ, classicalHillNormalizedNumerator N R n (lambda,t.2) = 0 ↔
    ∃ k : ℕ+, k ≠ n ∧ classicalHillCandidateEnergy N k t = lambda
  zeros_simple : ∀ lambda : ℂ, classicalHillNormalizedNumerator N R n (lambda,t.2) = 0 →
    deriv (fun w => classicalHillNormalizedNumerator N R n (w,t.2)) lambda ≠ 0

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem normalizedProductQuotient_constant
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R t.2 (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q t.2 (lp.single 2 j 1)) m)
    (hroots : ∀ k : ℕ+, k ≠ n →
      classicalHillNormalizedNumerator N R n (classicalHillCandidateEnergy N k t,t.2) = 0) :
    ∀ lambda : ℂ, classicalHillNormalizedProductQuotient N R n t lambda =
      classicalHillNormalizedLeadingCoefficient Q n t.2 := by
  have hwhole := (D.normalizedProductQuotient_entire R hRa n t ht haux hroots).1
  let L := classicalHillNormalizedLeadingCoefficient Q n t.2
  let F (z : ℂ) : ℂ := classicalHillNormalizedProductQuotient N R n t (z^2)-L
  have hF : Differentiable ℂ F := by
    intro z
    exact (((hwhole (z^2) (mem_univ _)).comp (f := fun z : ℂ => z^2)
      (analyticAt_id.pow 2)).sub analyticAt_const).differentiableAt
  let S := {z : ℂ // ∀ j : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*j‖}
  have hlim := D.tendsto_normalizedProductQuotient_of_separated R Q n t ht haux hcompat
    (fun z : S => z.val) tendsto_comap (by positivity : 0 < Real.pi/4) le_rfl (fun z => z.property)
  have hnorm : Tendsto (fun z : S => ‖F z.val‖)
      (comap (fun z : S => ‖z.val‖) atTop) (𝓝 0) := by
    simpa only [L,F,sub_self,norm_zero] using! (hlim.sub_const L).norm
  have hzero : F = 0 := by
    apply entire_eq_zero_of_small_on_expanding_circles hF centralCircleRadius tendsto_centralCircleRadius_atTop
    intro eps heps
    obtain ⟨K,hK⟩ := exists_threshold_of_eventually_comap_atTop
      (fun z : S => ‖z.val‖) (hnorm.eventually (gt_mem_nhds heps))
    filter_upwards [tendsto_centralCircleRadius_atTop.eventually_ge_atTop K] with k hk z hz
    have hsep : ∀ j : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*j‖ := by
      intro j
      have hb := centralCircle_lattice_gap k hz j
      linarith [Real.pi_pos]
    have hn : ‖z‖ = centralCircleRadius k := by simpa only [mem_sphere,dist_zero_right] using hz
    exact (hK ⟨z,hsep⟩ (by rw [hn]; exact hk)).le
  intro lambda
  have he := congrFun hzero (Complex.sqrt lambda)
  change classicalHillNormalizedProductQuotient N R n t ((Complex.sqrt lambda)^2)-L = 0 at he
  rw [sq_sqrt] at he
  exact sub_eq_zero.mp he

/-- Actual normalized numerators equal the literal omitted product times
their analytic leading scalar. -/
theorem normalizedNumerator_product_leading
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R t.2 (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q t.2 (lp.single 2 j 1)) m)
    (hroots : ∀ k : ℕ+, k ≠ n →
      classicalHillNormalizedNumerator N R n (classicalHillCandidateEnergy N k t,t.2) = 0)
    (lambda : ℂ) : classicalHillNormalizedNumerator N R n (lambda,t.2) =
      classicalHillNormalizedLeadingCoefficient Q n t.2*classicalHillCandidateOmittedProduct N n t lambda := by
  have hf := (D.normalizedProductQuotient_entire R hRa n t ht haux hroots).2 lambda
  rw [D.normalizedProductQuotient_constant R Q hRa n t ht haux hcompat hroots lambda] at hf
  exact hf.symm

/-- Simplicity of the actual selected zeros forces the leading scalar
nonzero, hence there are no additional normalized numerator zeros. -/
theorem normalizedNumerator_complete_zeros
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R t.2 (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q t.2 (lp.single 2 j 1)) m)
    (hroots : ∀ k : ℕ+, k ≠ n →
      classicalHillNormalizedNumerator N R n (classicalHillCandidateEnergy N k t,t.2) = 0 ∧
      deriv (fun lambda => classicalHillNormalizedNumerator N R n (lambda,t.2))
        (classicalHillCandidateEnergy N k t) ≠ 0) :
    classicalHillNormalizedLeadingCoefficient Q n t.2 ≠ 0 ∧
    (∀ lambda : ℂ, classicalHillNormalizedNumerator N R n (lambda,t.2) =
      classicalHillNormalizedLeadingCoefficient Q n t.2*classicalHillCandidateOmittedProduct N n t lambda) ∧
    ∀ lambda : ℂ, classicalHillNormalizedNumerator N R n (lambda,t.2) = 0 ↔
      ∃ k : ℕ+, k ≠ n ∧ classicalHillCandidateEnergy N k t = lambda := by
  have hzer := fun k hkn => (hroots k hkn).1
  have hconst := D.normalizedProductQuotient_constant R Q hRa n t ht haux hcompat hzer
  let k : ℕ+ := ⟨(n : ℕ)+1,by omega⟩
  have hkn : k ≠ n := by
    intro he
    have hi := congrArg (fun j : ℕ+ => (j : ℕ)) he
    change (n : ℕ)+1 = (n : ℕ) at hi
    omega
  have hL : classicalHillNormalizedLeadingCoefficient Q n t.2 ≠ 0 := by
    have hh := D.normalizedProductQuotient_ne_zero_at_selected_root R n k hkn t ht haux (hroots k hkn).2
    rwa [hconst] at hh
  have hf := D.normalizedNumerator_product_leading R Q hRa n t ht haux hcompat hzer
  refine ⟨hL,hf,?_⟩
  intro lambda
  rw [hf lambda,mul_eq_zero,or_iff_right hL]
  exact (D.candidate_omitted_product n t ht haux).2.2.1 lambda

/-- The literal energy products, multiplied by the proved leading scalar,
converge locally uniformly to the actual normalized entire numerator. -/
theorem normalizedNumerator_product_convergence
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R t.2 (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q t.2 (lp.single 2 j 1)) m)
    (hroots : ∀ k : ℕ+, k ≠ n →
      classicalHillNormalizedNumerator N R n (classicalHillCandidateEnergy N k t,t.2) = 0) :
    TendstoLocallyUniformlyOn
      (fun M lambda => classicalHillNormalizedLeadingCoefficient Q n t.2*
        classicalHillCandidateOmittedPartialProduct N n t lambda M)
      (fun lambda => classicalHillNormalizedNumerator N R n (lambda,t.2)) atTop univ := by
  let L : ℂ →L[ℂ] ℂ := classicalHillNormalizedLeadingCoefficient Q n t.2 • ContinuousLinearMap.id ℂ ℂ
  have hc := L.uniformContinuous.comp_tendstoLocallyUniformlyOn (D.candidate_omitted_product n t ht haux).2.1
  have hc' : TendstoLocallyUniformlyOn
      (fun M lambda => classicalHillNormalizedLeadingCoefficient Q n t.2*classicalHillCandidateOmittedPartialProduct N n t lambda M)
      (fun lambda => classicalHillNormalizedLeadingCoefficient Q n t.2*classicalHillCandidateOmittedProduct N n t lambda) atTop univ := by
    simpa only [L,Function.comp_def,smul_apply,smul_eq_mul,ContinuousLinearMap.id_apply] using! hc
  exact hc'.congr_right (fun lambda _ => (D.normalizedNumerator_product_leading R Q hRa n t ht haux hcompat hroots lambda).symm)

theorem normalized_product_data
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R t.2 (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q t.2 (lp.single 2 j 1)) m)
    (hroots : ∀ k : ℕ+, k ≠ n →
      classicalHillNormalizedNumerator N R n (classicalHillCandidateEnergy N k t,t.2) = 0 ∧
      deriv (fun lambda => classicalHillNormalizedNumerator N R n (lambda,t.2))
        (classicalHillCandidateEnergy N k t) ≠ 0) :
    ClassicalNormalizedProductData N R Q n t := by
  have hzer := fun k hkn => (hroots k hkn).1
  have hc := D.normalizedNumerator_complete_zeros R Q hRa n t ht haux hcompat hroots
  refine ⟨hc.1,D.normalizedProductQuotient_constant R Q hRa n t ht haux hcompat hzer,hc.2.1,
    D.normalizedNumerator_product_convergence R Q hRa n t ht haux hcompat hzer,hc.2.2,?_⟩
  intro lambda hz
  obtain ⟨k,hkn,hk⟩ := (hc.2.2 lambda).mp hz
  rw [← hk]
  exact (hroots k hkn).2

end ClassicalAllContourPeriodData
/-- One actual normalization neighborhood precedes the omitted mode. Each
mode has an analytic infinite root branch with complete simple Psi_n zeros
and a proved nonzero analytic scalar multiplying the literal energy product. -/
theorem exists_classicalHill_local_complete_normalized_products :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ),
      ∃ R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ AnalyticOnNhd ℂ R V ∧ AnalyticOnNhd ℂ Q V ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧ Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        (∀ n : ℕ+, AnalyticOnNhd ℂ (classicalHillNormalizedLeadingCoefficient Q n) V ∧
          classicalHillNormalizedLeadingCoefficient Q n 0 = 1) ∧
        (∀ n k : ℕ+, ∀ q ∈ V,
          (2*(Real.pi : ℂ))⁻¹ * ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
            classicalHillNormalizedNumerator N R n (z^2,q)/classicalHillContinuedRoot (z^2,q)*(2*z) =
              if n = k then 1 else 0) ∧
        ∀ n : ℕ+, ∃ U : Set (NLS.LinearVolterra.Curve ℂ), ∃ s : NLS.LinearVolterra.Curve ℂ → NLS.Coeff 2,
          U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧ s 0 = 0 ∧ AnalyticOnNhd ℂ s U ∧
          (∀ k : ℕ+, AnalyticOnNhd ℂ (fun q => classicalHillCandidateEnergy N k (s q,q)) U) ∧
          (∀ k : ℕ+, classicalHillCandidateEnergy N k (s 0,0) = freeHillEnergy k) ∧
          ∀ q ∈ U, ‖s q‖ < Real.pi/16 ∧
            (∀ j : ℤ, j ≤ 0 ∨ j = (n : ℤ) → s q j = 0) ∧
            ClassicalNormalizedProductData N R Q n (s q,q) := by
  obtain ⟨N,V,T,R,S,Q,hN,hV,h0V,_,hRa,_,hQa,_,hR0,_,hQ0,hinv,hentry,hcompat,A,D⟩ :=
    exists_classicalHill_twoWeighted_period_inverse
  refine ⟨N,V,R,Q,hN,hV,h0V,hRa,hQa,hR0,hQ0,?_,?_,?_⟩
  · intro n
    exact ⟨classicalHillNormalizedLeadingCoefficient_analytic Q V hQa n,
      classicalHillNormalizedLeadingCoefficient_free Q hQ0 n⟩
  · intro n k q hq
    exact D.normalizedNumerator_period n k q hq T R (fun m j => (hentry q hq m j).1) (hinv q hq).1
  intro n
  obtain ⟨U,s,hUV,hU,h0,hs0,hsa,henergy,hfree,hs⟩ :=
    D.exists_actual_simple_normalized_zero_family R Q hRa hQa
      (fun q hq => (hinv q hq).2.2.2.2.2) hQ0 hcompat n
  refine ⟨U,s,hUV,hU,h0,hs0,hsa,henergy,hfree,?_⟩
  intro q hq
  have ht : (s q,q) ∈ classicalHillCandidateDomain V :=
    ⟨by simpa only [mem_ball,dist_zero_right] using (hs q hq).1,hUV hq⟩
  have haux : ∀ j ≤ (0 : ℤ), s q j = 0 := fun j hj => (hs q hq).2.1 j (Or.inl hj)
  exact ⟨(hs q hq).1,(hs q hq).2.1,D.normalized_product_data R Q hRa n (s q,q) ht haux
    (hcompat q (hUV hq)) (hs q hq).2.2.2⟩

end NLS.KdV
