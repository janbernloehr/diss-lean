import NLS.KdV.MiuraDiagonalFrequencySymbol
import NLS.KdV.PhysicalDiagonalActionCancellation

/-! The actual corrected physical diagonal contribution is six times
the original action times a bounded analytic Hilbert symbol, on one
full complex rough-source neighborhood of every real base. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.PhysicalMiuraFrequencyChart

theorem exists_local_diagonal_frequency_symbol
    (B : PhysicalMiuraFrequencyChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      B.psi.family.originalDomain B.psi.family.domain B.psi.family.roots)
    (q0 : PeriodOneHminusOne) (hq0 : q0∈B.domain) (hr0 : IsRealPeriodOneHminusOne q0) :
    ∃ T : Set PeriodOneHminusOne, IsOpen T ∧ q0∈T ∧ T⊆B.domain ∧
      ∃ M : ℝ, 0≤M ∧ ∃ S : PeriodOneHminusOne → Coeff 2,
        AnalyticOnNhd ℂ S T ∧ (∀ q∈T, ‖S q‖≤M) ∧
        (∀ q∈T, ∀ j : ℤ, j≤0 → S q j=0) ∧
        ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val∈T → ∀ n : ℕ+,
          B.correction n (hillOriginalHminusSource p.val)+
              6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n : ℕ) 0 : ℂ)=
            B.offDiagonalCorrection n (hillOriginalHminusSource p.val)+
              6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n : ℕ) 0 : ℂ)*
                S (hillOriginalHminusSource p.val) (n : ℤ) := by
  let F := fun q : PeriodOneHminusOne => hillMiuraDiagonal (B.psi.miura.lift q)
  let u : PeriodOneRealL2 := ⟨B.psi.miura.lift q0,B.real_lift q0 (B.domain_subset hq0).1 hr0⟩
  let φ := hillMiuraRealSource u
  have hs := H.angular_extension
  obtain ⟨D,_hD⟩ := B.atlas.exists_errorDomain hs.toSourcePsiNormalizedComplexExtension
    B.psi.family.domain_open B.psi.family.real_subset
  obtain ⟨W,_hW,_hrealW,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num)
  obtain ⟨C,hcenter⟩ := hfamilies φ
  have hC : φ.val∈ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨U,hU,hqU,_hsubU,M,hM,σ,hσ,hσb,hσzero,_hσraw,hfactor⟩ :=
    exists_Miura_diagonal_frequency_symbol C hs B.psi.family.domain_open B.atlas D u
      (B.psi.family.real_subset φ.property) hC
  have hF : AnalyticOnNhd ℂ F B.domain := fun q hq =>
    (hillMiuraDiagonal.analyticAt _).comp (B.psi.miura.lift_analytic q (B.domain_subset hq).1)
  let T := B.domain∩F ⁻¹' U
  have hT : IsOpen T := hF.continuousOn.isOpen_inter_preimage B.domain_open hU
  let S := fun q => σ (F q)
  refine ⟨T,hT,⟨hq0,hqU⟩,inter_subset_left,M,hM,S,?_,?_,?_,?_⟩
  · intro q hq
    exact (hσ (F q) hq.2).comp (hF q hq.1)
  · intro q hq
    exact hσb (F q) hq.2
  · intro q hq j hj
    exact hσzero (F q) hq.2 j hj
  · intro p hp n
    have hc := hfactor (B.psi.miura.lift (hillOriginalHminusSource p.val)) hp.2 n
    have hI := B.psi.original_action_eq_twice_weighted_Dirac p (B.domain_subset hp.1) B.real_lift
      (B.outside_shift _ (B.domain_subset hp.1).1) B.shift B.energyShift_eq n
    rw [hI]
    unfold correction offDiagonalCorrection
    change -12*B.atlas.weightedSecondMomentSum (n : ℤ) (F (hillOriginalHminusSource p.val))+
      6*(2*sourceComplexHigherAction (by norm_num) (by norm_num) (n : ℤ) 1 (F (hillOriginalHminusSource p.val)))=
      (-12)*(B.atlas.weightedSecondMomentSum (n : ℤ) (F (hillOriginalHminusSource p.val))-
        (n : ℂ)*(B.atlas.moment (n : ℤ) (n : ℤ) 2 (F (hillOriginalHminusSource p.val))-
          B.atlas.moment (n : ℤ) (-(n : ℤ)) 2 (F (hillOriginalHminusSource p.val))))+
        6*(2*sourceComplexHigherAction (by norm_num) (by norm_num) (n : ℤ) 1 (F (hillOriginalHminusSource p.val)))*
          σ (F (hillOriginalHminusSource p.val)) (n : ℤ)
    linear_combination hc

end NLS.KdV.PhysicalMiuraFrequencyChart
