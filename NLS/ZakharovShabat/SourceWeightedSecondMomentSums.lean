import NLS.ZakharovShabat.SourceWeightedSecondMomentSequences
import NLS.SequenceSpaces.LocallyUniformSummation
import NLS.ZakharovShabat.SourceAbelianMomentSquaredGapAtlas

/-! # Actual analytic signed index-weighted second-moment sums -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The literal signed integer-weighted second-moment sum. It is not
identified here with a physical KdV frequency. -/
def SourceAbelianMomentAtlas.weightedSecondMomentSum
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (n : ℤ) (ψ : CoeffPair 2) : ℂ :=
  ∑' k : ℤ, (k : ℂ)*A.moment n k 2 ψ

theorem SourceAbelianMomentAtlas.exists_analytic_weightedSecondMomentSum
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2 ⊆ V) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 2 ⊆ U ∧
      U ⊆ A.domain ∩ V ∧
      (∀ ψ ∈ U, ∀ n : ℤ, Summable (fun k : ℤ => ‖(k : ℂ)*A.moment n k 2 ψ‖)) ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (A.weightedSecondMomentSum n) U) ∧
      (∀ n : ℤ, TendstoLocallyUniformlyOn
        (fun (N : ℕ) ψ => ∑ k ∈ Finset.Icc (-(N : ℤ)) N, (k : ℂ)*A.moment n k 2 ψ)
        (A.weightedSecondMomentSum n) atTop U) ∧
      ∀ φ ∈ U, ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∀ n : ℤ,
          ‖A.weightedSecondMomentSum n ψ‖ ≤ (1+‖(n : ℂ)‖)*C := by
  obtain ⟨U,hU,hUc,hreal,hUV,ha,hcoeff,hlocal⟩ :=
    A.exists_analytic_weightedSecondMomentTerms hs hV hrealV
  have hsum (ψ : CoeffPair 2) (hψ : ψ ∈ U) (n : ℤ) :
      Summable (fun k : ℤ => ‖(k : ℂ)*A.moment n k 2 ψ‖) := by
    have hh := (lp.memℓp (A.weightedSecondMomentTerms n ψ)).summable (by norm_num : 0<(1 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_one,Real.rpow_one,hcoeff ψ hψ] using hh
  have he (ψ : CoeffPair 2) (hψ : ψ ∈ U) (n : ℤ) :
      (lp.tsumCLM ℂ ℤ ℂ) (A.weightedSecondMomentTerms n ψ)=A.weightedSecondMomentSum n ψ := by
    change (∑' k : ℤ, A.weightedSecondMomentTerms n ψ k)=_
    simp only [hcoeff ψ hψ,weightedSecondMomentSum]
  have han (n : ℤ) : AnalyticOnNhd ℂ (A.weightedSecondMomentSum n) U := by
    intro ψ hψ
    have hh := ((lp.tsumCLM ℂ ℤ ℂ).analyticAt _).comp (ha n ψ hψ)
    exact hh.congr (Filter.eventuallyEq_of_mem (hU.mem_nhds hψ) (fun χ hχ => he χ hχ n))
  have hconv (n : ℤ) : TendstoLocallyUniformlyOn
      (fun (N : ℕ) ψ => ∑ k ∈ Finset.Icc (-(N : ℤ)) N, (k : ℂ)*A.moment n k 2 ψ)
      (A.weightedSecondMomentSum n) atTop U := by
    have hh := Coeff.tendstoLocallyUniformlyOn_sums_of_continuousOn
      (A.weightedSecondMomentTerms n) U (ha n).continuousOn
    rw [Metric.tendstoLocallyUniformlyOn_iff] at hh ⊢
    intro ε hε ψ hψ
    obtain ⟨T,hT,hb⟩ := hh ε hε ψ hψ
    refine ⟨T ∩ U,inter_mem hT self_mem_nhdsWithin,hb.mono ?_⟩
    intro N hN χ hχ
    simpa only [hcoeff χ hχ.2,weightedSecondMomentSum] using hN χ hχ.1
  refine ⟨U,hU,hUc,hreal,hUV,hsum,han,hconv,?_⟩
  intro φ hφ
  obtain ⟨T,hT,hφT,hTU,C,hC,hbound⟩ := hlocal φ hφ
  refine ⟨T,hT,hφT,hTU,C,hC,?_⟩
  intro ψ hψ n
  rw [←he ψ (hTU hψ) n]
  exact (lp.norm_tsum_le _).trans (hbound ψ hψ n)

/-- The actual atlas and the compatible squared-gap branch are both
constructed. Thus the weighted sum exists analytically near EVERY real
Hilbert source with no atlas or period-normalization hypothesis supplied. -/
theorem exists_actual_analytic_weighted_secondMoment_sums :
    ∃ W V : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
      ∃ A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s,
      ∃ U : Set (CoeffPair 2), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 2 ⊆ U ∧
        U ⊆ A.domain ∩ V ∧
        (∀ ψ ∈ U, ∀ n : ℤ, Summable (fun k : ℤ => ‖(k : ℂ)*A.moment n k 2 ψ‖)) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (A.weightedSecondMomentSum n) U) ∧
        (∀ n : ℤ, TendstoLocallyUniformlyOn
          (fun (N : ℕ) ψ => ∑ k ∈ Finset.Icc (-(N : ℤ)) N, (k : ℂ)*A.moment n k 2 ψ)
          (A.weightedSecondMomentSum n) atTop U) ∧
        ∀ φ ∈ U, ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
          ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∀ n : ℤ,
            ‖A.weightedSecondMomentSum n ψ‖ ≤ (1+‖(n : ℂ)‖)*C := by
  obtain ⟨W,V,_hW,_hrealW,hV,hrealV,s,hs,⟨A⟩⟩ :=
    exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by norm_num) (by norm_num)
  obtain ⟨U,hU,hUc,hreal,hUV,hsum,han,hconv,hbound⟩ :=
    A.exists_analytic_weightedSecondMomentSum hs hV hrealV
  exact ⟨W,V,s,A,U,hU,hUc,hreal,hUV,hsum,han,hconv,hbound⟩

end NLS.ZakharovShabat
