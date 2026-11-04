import NLS.SequenceSpaces.WeightedReciprocalRows
import NLS.SequenceSpaces.LocallyBoundedRealization
import NLS.ZakharovShabat.SourceAbelianMomentOnePlusDomain
import NLS.ZakharovShabat.SourceAbelianMomentLemma20_3

/-! # Analytic absolutely summable weighted moment rows

The sharp off-diagonal bound and the actual diagonal formula provide a
locally bounded ℓ¹ realization of the full weighted row. Coordinatewise
moment analyticity then gives analyticity in the ℓ¹ norm. The same local
constant controls every row after division by 1 + |n|.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W W₀ V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The total realization retains every actual moment on its membership domain. -/
def SourceAbelianMomentAtlas.weightedSecondMomentRow
    (A : SourceAbelianMomentAtlas hp hp1 W s) (n : ℤ) (ψ : CoeffPair p) : Coeff 1 :=
  Coeff.ofFunctionOrZero 1 (fun k => (k:ℂ)*A.moment n k 2 ψ)

/-- The weighted rows are genuine analytic ℓ¹ maps with locally uniform
linear growth in the selected index, on one constructed common domain. -/
theorem SourceAbelianMomentAtlas.exists_analytic_weightedSecondMomentRows
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (H : SourceLemma12_11Data hp hp1 W₀ V s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧
      (∀ ψ ∈ U, ∀ n k : ℤ, A.weightedSecondMomentRow n ψ k = (k:ℂ)*A.moment n k 2 ψ) ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (A.weightedSecondMomentRow n) U) ∧
      ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∀ n : ℤ,
          ‖A.weightedSecondMomentRow n ψ‖ ≤ (|(n:ℝ)|+1)*C := by
  obtain ⟨Uo,hUo,_,hrealO,hOV,hoff⟩ := A.exists_offDiagonal_onePlus_all H hs hV hrealV
  obtain ⟨Ud,hUd,_,hrealD,_,hdiag⟩ := A.exists_lemma20_3_refined hs hV hrealV
  let U := connectedComponentIn (Uo ∩ Ud) (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealS : realTypeSourceLocus p ⊆ Uo ∩ Ud := fun ψ hψ => ⟨hrealO hψ,hrealD hψ⟩
  have hUS : U ⊆ Uo ∩ Ud := connectedComponentIn_subset _ _
  have hU : IsOpen U := (hUo.inter hUd).connectedComponentIn
  have hUA : U ⊆ A.domain ∩ V := fun ψ hψ => hOV (hUS hψ).1
  have hpc1 : 1 < p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hpc : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  let : Fact (1 ≤ p.conjExponent) := ⟨hpc1.le⟩
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    conv_rhs => rw [← ENNReal.ofReal_toReal hp]
    exact ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := p)])
  have hlocal (φ : CoeffPair p) (hφ : φ ∈ U) :
      ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∀ n : ℤ, ∃ b : Coeff 1,
          (∀ k, b k = (k:ℂ)*A.moment n k 2 ψ) ∧ ‖b‖ ≤ (|(n:ℝ)|+1)*C := by
    obtain ⟨To,hTo,hφTo,_,ho⟩ := hoff φ (hUS hφ).1
    obtain ⟨M,hM,hrows⟩ := ho p.conjExponent hpc hpc1
    obtain ⟨ρ,hρ,_,hd⟩ := hdiag φ (hUS hφ).2
    obtain ⟨Md,hMd,hdata⟩ := hd p hp hp1 hhalf
    obtain ⟨_,_,Tg,hTg,hφg,G,hG,hg⟩ :=
      exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
    let T := ((To ∩ ball φ ρ) ∩ Tg) ∩ U
    let D := G^2/4*(Real.pi+Md)
    have hD : 0 ≤ D := by dsimp [D]; positivity
    refine ⟨T,((hTo.inter isOpen_ball).inter hTg).inter hU,
      ⟨⟨⟨hφTo,mem_ball_self hρ⟩,hφg⟩,hφ⟩,inter_subset_right,
      G^3*M+D,by positivity,?_⟩
    intro ψ hψ n
    obtain ⟨a,_,_,ha,hformula⟩ := hrows ψ hψ.1.1.1 n
    obtain ⟨d,_,hdnorm,hdfactor,_⟩ := hdata ψ hψ.1.1.2
    have hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ ≤ G := (hg ψ hψ.1.2).1
    have hdi : ‖A.moment n n 2 ψ‖ ≤ D := by
      have hgn := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' _ n).trans hgap
      have hdn := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' d n).trans hdnorm
      have hsum : ‖(Real.pi:ℂ)+d n‖ ≤ Real.pi+Md := by
        apply (norm_add_le _ _).trans
        simpa only [Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le] using add_le_add le_rfl hdn
      rw [hdfactor n,norm_mul,norm_div,norm_pow]
      norm_num only [Complex.norm_ofNat]
      exact mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hgn 2) (by norm_num))
        hsum (norm_nonneg _) (by positivity)
    obtain ⟨b,hb,hbn⟩ := Coeff.exists_weighted_cubic_reciprocal_row hp hp1
      (sourcePeriodicGapDisplacement hp hp1 ψ) a n (fun k => A.moment n k 2 ψ) hformula
    refine ⟨b,hb,hbn.trans ?_⟩
    have hfirst : (|(n:ℝ)|+1)*‖sourcePeriodicGapDisplacement hp hp1 ψ‖^3*‖a‖ ≤
        (|(n:ℝ)|+1)*G^3*M := by gcongr
    have hlast : ‖(n:ℂ)*A.moment n n 2 ψ‖ ≤ |(n:ℝ)| *D := by
      rw [norm_mul,Complex.norm_intCast]
      exact mul_le_mul_of_nonneg_left hdi (abs_nonneg _)
    exact (add_le_add hfirst hlast).trans (by nlinarith)
  have han (n : ℤ) := Coeff.analytic_realization_of_local_bounds
    (r := 1) (fun ψ k => (k:ℂ)*A.moment n k 2 ψ) hU
    (fun k ψ hψ => analyticAt_const.mul (A.analytic_moment n k 2 ψ (hUA hψ).1)) (by
      intro φ hφ
      obtain ⟨T,hT,hφT,hTU,C,_,hb⟩ := hlocal φ hφ
      exact ⟨T,hT,hφT,hTU,(|(n:ℝ)|+1)*C,fun ψ hψ => hb ψ hψ n⟩)
  refine ⟨U,hU,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS,
    hUA,fun ψ hψ n k => (han n).1 ψ hψ k,fun n => (han n).2,?_⟩
  intro φ hφ
  obtain ⟨T,hT,hφT,hTU,C,hC,hb⟩ := hlocal φ hφ
  refine ⟨T,hT,hφT,hTU,C,hC,?_⟩
  intro ψ hψ n
  obtain ⟨b,hb,hn⟩ := hb ψ hψ n
  change ‖Coeff.ofFunctionOrZero 1 _‖ ≤ _
  rwa [Coeff.ofFunctionOrZero_eq_of_coordinates _ b hb]

end NLS.ZakharovShabat
