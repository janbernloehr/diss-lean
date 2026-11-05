import NLS.ZakharovShabat.SourceCanonicalCoefficientContinuity
import NLS.ZakharovShabat.SourceDiscriminantCoefficientContinuity
import NLS.ZakharovShabat.SourcePrimitivePowerPositive
import NLS.ComplexAnalysis.CompactJointLimits
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! # Real gap profiles under bounded coefficient limits

The actual indexed endpoints and entire discriminants converge under
bounded Fourier limits. Evaluation at the moving cosine coordinate then
gives convergence of the true arcosh profile, including its endpoints
and collapsed gaps. Compact parameter intervals give uniform convergence.
-/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem tendsto_realGapAffinePoint_cos_of_bounded_coefficientwise
    {A : Type*} {l : Filter A} (φ : A → CoeffPair 2) (ψ : CoeffPair 2)
    (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax 2 (φ k))) (hψ : IsRealType (CoeffPair.toMax 2 ψ))
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (n : ℤ) (θ : A → ℝ) (t : ℝ) (hθ : Tendsto θ l (𝓝 t)) :
    Tendsto (fun k => realGapAffinePoint (by simp) (by norm_num) (φ k) n (Real.cos (θ k))) l
      (𝓝 (realGapAffinePoint (by simp) (by norm_num) ψ n (Real.cos t))) := by
  have he := tendsto_source_canonicalPeriodicEndpoints_of_bounded_coefficientwise
    (by simp) (by norm_num) φ ψ hb hφ hψ ht n
  have hL := continuous_re.continuousAt.tendsto.comp he.1
  have hR := continuous_re.continuousAt.tendsto.comp he.2
  exact ((hL.add hR).div_const 2).add
    (((hR.sub hL).div_const 2).mul (Real.continuous_cos.continuousAt.tendsto.comp hθ))

theorem tendsto_sourceRealGapCosineProfile_of_bounded_coefficientwise
    {A : Type*} {l : Filter A} (φ : A → CoeffPair 2) (ψ : CoeffPair 2)
    (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax 2 (φ k))) (hψ : IsRealType (CoeffPair.toMax 2 ψ))
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (n : ℤ) (θ : A → ℝ) (t : ℝ) (hθ : Tendsto θ l (𝓝 t)) :
    Tendsto (fun k => sourceRealGapCosineProfile (by simp) (by norm_num) (φ k) n (θ k)) l
      (𝓝 (sourceRealGapCosineProfile (by simp) (by norm_num) ψ n t)) := by
  let x : A → ℝ := fun k => realGapAffinePoint (by simp) (by norm_num) (φ k) n (Real.cos (θ k))
  let y := realGapAffinePoint (by simp) (by norm_num) ψ n (Real.cos t)
  have hx : Tendsto x l (𝓝 y) :=
    tendsto_realGapAffinePoint_cos_of_bounded_coefficientwise φ ψ hb hφ hψ ht n θ t hθ
  have hd := tendstoLocallyUniformly_sourceDiscriminant_of_bounded_coefficientwise φ ψ hb ht
    (tendsto_source_snd_of_realType_coefficientwise φ ψ hφ hψ ht)
  have hD := hd.tendsto_comp
    ((analyticOnNhd_canonicalDiscriminant (by simp) (by norm_num) (periodOnePotential ψ)
      (periodOnePotential_mem ψ) (y : ℂ) (mem_univ _)).continuousAt)
    (continuous_ofReal.continuousAt.tendsto.comp hx)
  have hhalf : Tendsto (fun k => realGapHalfDiscriminant (by simp) (periodOnePotential (φ k)) n (x k)) l
      (𝓝 (realGapHalfDiscriminant (by simp) (periodOnePotential ψ) n y)) := by
    by_cases hn : n % 2 = 0
    · simpa only [realGapHalfDiscriminant,if_pos hn,Function.comp_def] using!
        (continuous_re.continuousAt.tendsto.comp hD).div_const 2
    · simpa only [realGapHalfDiscriminant,if_neg hn,Function.comp_def] using!
        (continuous_re.continuousAt.tendsto.comp hD).neg.div_const 2
  have hge (k : A) : 1 ≤ realGapHalfDiscriminant (by simp) (periodOnePotential (φ k)) n (x k) :=
    realGapHalfDiscriminant_one_le_on_gap (by simp) (by norm_num) (φ k) (hφ k) n (x k)
      (realGapAffinePoint_cos_mem_Icc (by simp) (by norm_num) ⟨φ k,hφ k⟩ n (θ k))
  have hgeψ : 1 ≤ realGapHalfDiscriminant (by simp) (periodOnePotential ψ) n y :=
    realGapHalfDiscriminant_one_le_on_gap (by simp) (by norm_num) ψ hψ n y
      (realGapAffinePoint_cos_mem_Icc (by simp) (by norm_num) ⟨ψ,hψ⟩ n t)
  exact (Real.continuousOn_arcosh _ hgeψ).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hhalf,Eventually.of_forall hge⟩)

/-- The moving profile converges uniformly on every compact real parameter set. -/
theorem tendstoUniformlyOn_sourceRealGapCosineProfile_of_bounded_coefficientwise
    {A : Type*} {l : Filter A} (φ : A → CoeffPair 2) (ψ : CoeffPair 2)
    (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax 2 (φ k))) (hψ : IsRealType (CoeffPair.toMax 2 ψ))
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (n : ℤ) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun k => sourceRealGapCosineProfile (by simp) (by norm_num) (φ k) n)
      (sourceRealGapCosineProfile (by simp) (by norm_num) ψ n) l K := by
  apply NLS.ComplexAnalysis.tendstoUniformlyOn_of_joint_limits hK
    (sourceRealGapCosineProfile_continuous (by simp) (by norm_num) ⟨ψ,hψ⟩ n).continuousOn
  intro t _
  exact tendsto_sourceRealGapCosineProfile_of_bounded_coefficientwise
    (fun q : A × ℝ => φ q.1) ψ (hb.subset (range_comp_subset_range Prod.fst φ))
    (fun q => hφ q.1) hψ (fun j => (ht j).comp tendsto_fst) n Prod.snd t
    (tendsto_snd.mono_right nhdsWithin_le_nhds)

end NLS.ZakharovShabat
