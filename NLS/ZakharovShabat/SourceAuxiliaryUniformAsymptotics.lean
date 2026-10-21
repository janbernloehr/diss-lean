import NLS.ZakharovShabat.SourceDirichletOmittedNormalizedAnalytic
import NLS.SequenceSpaces.NormalizedInverseAnalytic
import NLS.SequenceSpaces.Multiplier

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def auxiliaryParitySymbol : Coeff ⊤ :=
  ⟨fun n => (-1:ℂ)^n.natAbs,memℓp_infty ⟨1,by rintro _ ⟨n,rfl⟩; simp⟩⟩

/-- The complete auxiliary normalization error in the original lp norm. -/
def sourceGapWeightedEtaAuxiliaryRemainder (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Coeff p :=
  -(Coeff.multiplierCLM auxiliaryParitySymbol)
    (Coeff.ofFunctionOrZero p (fun n => (sourceDirichletOmittedNormalized hp hp1 ψ n)⁻¹-1))

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The corrected source auxiliary has an analytic full lp error on the original W. -/
theorem auxiliary_remainder_analytic (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    AnalyticOnNhd ℂ (sourceGapWeightedEtaAuxiliaryRemainder hp hp1) W ∧
      ∀ ψ ∈ W, ∀ n, sourceGapWeightedEtaAuxiliaryRemainder hp hp1 ψ n =
        2*sourceGapWeightedEtaAuxiliary hp hp1 n ψ+cos ((Real.pi:ℂ)*n) := by
  obtain ⟨hf,hfv⟩ := H.dirichlet_omitted_normalized_analytic
  obtain ⟨hg,hgv⟩ := Coeff.analytic_normalized_inverse_error hp
    H.original_theta_common_domain.source_open (sourceDirichletOmittedNormalized hp hp1)
    (fun n ψ hψ => analyticAt_const.mul (H.dirichlet_omitted_sample_data ψ hψ n).2)
    (fun ψ hψ n => mul_ne_zero (pow_ne_zero _ (by norm_num))
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ _ n
        (H.dirichlet_omitted_sample_data ψ hψ n).1))
    (fun ψ => Coeff.ofFunctionOrZero p (fun n => sourceDirichletOmittedNormalized hp hp1 ψ n-1))
    hf.continuousOn hfv
  refine ⟨fun ψ hψ => (((Coeff.multiplierCLM (p := p) auxiliaryParitySymbol).analyticAt _).comp
    (hg ψ hψ)).neg,?_⟩
  intro ψ hψ n
  change -(auxiliaryParitySymbol n * Coeff.ofFunctionOrZero p
    (fun m => (sourceDirichletOmittedNormalized hp hp1 ψ m)⁻¹-1) n) = _
  rw [hgv ψ hψ n,cos_freeCenter_eq_natAbs_sign]
  let P := sourceStandardRootOmittedProduct hp hp1 n ψ
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
  let a : ℂ := (-1:ℂ)^n.natAbs
  have ha : a*a = 1 := by
    dsimp only [a]
    rw [← pow_two,← pow_mul,mul_comm n.natAbs 2,pow_mul]
    norm_num
  have hai : a⁻¹ = a := by simp only [a,← inv_pow,inv_neg,inv_one]
  change -(a*((a*P)⁻¹-1)) = 2*(-(2*P)⁻¹)+a
  rw [mul_inv_rev,mul_inv_rev,hai]
  calc
    -(a*(P⁻¹*a-1)) = -(a*a)*P⁻¹+a := by ring
    _ = 2*(-(P⁻¹*2⁻¹))+a := by rw [ha]; ring

/-- Membership is for the literal sequence, including every central and signed index. -/
theorem auxiliary_error_memlp (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    Memℓp (fun n => 2*sourceGapWeightedEtaAuxiliary hp hp1 n ψ+cos ((Real.pi:ℂ)*n)) p := by
  have heq : (fun n => sourceGapWeightedEtaAuxiliaryRemainder hp hp1 ψ n) =
      (fun n => 2*sourceGapWeightedEtaAuxiliary hp hp1 n ψ+cos ((Real.pi:ℂ)*n)) :=
    funext (H.auxiliary_remainder_analytic.2 ψ hψ)
  rw [← heq]
  exact lp.memℓp (sourceGapWeightedEtaAuxiliaryRemainder hp hp1 ψ)

/-- One original-source neighborhood bounds the entire auxiliary error sequence. -/
theorem auxiliary_error_local_bound (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ ψ ∈ U,
        ‖sourceGapWeightedEtaAuxiliaryRemainder hp hp1 ψ‖ ≤ B := by
  have hc := (H.auxiliary_remainder_analytic.1 φ hφ).continuousAt
  have hb : ∀ᶠ ψ in 𝓝 φ, ‖sourceGapWeightedEtaAuxiliaryRemainder hp hp1 ψ‖ <
      ‖sourceGapWeightedEtaAuxiliaryRemainder hp hp1 φ‖+1 :=
    hc.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨U,hUsub,hU,hφU⟩ := _root_.mem_nhds_iff.mp
    (inter_mem (H.original_theta_common_domain.source_open.mem_nhds hφ) hb)
  refine ⟨U,hU,hφU,fun ψ hψ => (hUsub hψ).1,
    ‖sourceGapWeightedEtaAuxiliaryRemainder hp hp1 φ‖+1,by positivity,?_⟩
  exact fun ψ hψ => (hUsub hψ).2.le

end SourceLemma12_12Data
end NLS.ZakharovShabat
