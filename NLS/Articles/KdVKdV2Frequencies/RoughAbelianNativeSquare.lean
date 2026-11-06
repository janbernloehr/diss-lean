import NLS.Articles.KdVKdV2Frequencies.RoughUniformActionAmplitudes
import NLS.KdV.HillHminusSourceAbelianSquare
import NLS.SequenceSpaces.HolderEmbedding

/-! # A common native rough Abelian sequence with exact physical squares

The gap-weighted own eta sequence absorbs the selected regular phase.
The amplitude, normalized midpoint and complete noncentral beta factor are
assembled in their native Banach norms before any output index is chosen.
The remaining indexwise sign is fixed separately by physical analytic germs.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

theorem exists_hillHminus_native_abelian_squared_packet :
    ∃ η C : ℝ, ∃ G : PeriodOneHminusOne → Coeff 2,
      0 < η ∧ 0 < C ∧ AnalyticOnNhd ℂ G (ball (0 : PeriodOneHminusOne) η) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, ‖G q‖ ≤ C ∧ ∀ j : ℤ, j ≤ 0 → G q j=0) ∧
      ∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
          (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)≠0 →
        (G (hillPhysicalHminusEmbedding p).val (n : ℤ))^2=
          (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos)^2/(1+(n : ℕ) : ℂ) := by
  classical
  obtain ⟨P,c,_hc,_hMc,hshift,h0P,hreal,houtside,H⟩ :=
    exists_hillHminusPsiChart_real_form_outside_shift (0 : PeriodOneHminusOne) (by intro j; simp) 0
  have h0B := P.mem_sourceBetaDomain_of_real 0 h0P (hreal 0 h0P.1 (by intro j; simp))
  obtain ⟨r,CA,A,hr,hCA,hAa,hAb,_hA0,hAp⟩ := exists_hillHminus_native_action_amplitude_symbol
  obtain ⟨Ur,hUr,h0Ur,hUrP,CR,R,hCR,hRa,hR⟩ := P.exists_local_native_sourceNormalizedMidpoint H 0 h0B
  obtain ⟨Ub,hUb,h0Ub,hUbP,CB,B,hCB,hBa,hB⟩ := P.exists_local_native_sourceNoncentralBeta_exp H 0 h0B
  obtain ⟨Ve,hVe,h0Ve,_hVeW,CE,hCE,_hEa,hE⟩ :=
    H.gapWeighted_original_local_sequence (P.dirichletSource 0) h0B.2
  let Ue := P.sourceBetaDomain ∩ P.dirichletSource ⁻¹' Ve
  have hc : ContinuousOn P.dirichletSource P.sourceBetaDomain :=
    P.analyticOnNhd_dirichletSource.continuousOn.mono inter_subset_left
  have hUe : IsOpen Ue := hc.isOpen_inter_preimage P.sourceBetaDomain_open hVe
  let U := ball (0 : PeriodOneHminusOne) r ∩ Ur ∩ Ub ∩ Ue
  have hU : IsOpen U := ((isOpen_ball.inter hUr).inter hUb).inter hUe
  have h0U : (0 : PeriodOneHminusOne)∈U := ⟨⟨⟨mem_ball_self hr,h0Ur⟩,h0Ub⟩,h0B,h0Ve⟩
  let G : PeriodOneHminusOne → Coeff 2 := fun q =>
    Coeff.holderProduct (q := 2) (A q)
      (Coeff.holderProduct (q := 2) (R q)
        (Coeff.holderProduct (q := 2) (B q) (P.sourceEtaSequence q)))
  have hGa : AnalyticOnNhd ℂ G U := by
    intro q hq
    have hinner := ((Coeff.holderProduct (p := ⊤) (r := 2) (q := 2)).analyticAt_bilinear _).comp₂
      (hBa q hq.1.2) (P.analytic_sourceEtaSequence H q hq.2.1)
    have hmiddle := ((Coeff.holderProduct (p := ⊤) (r := 2) (q := 2)).analyticAt_bilinear _).comp₂
      (hRa q hq.1.1.2) hinner
    exact ((Coeff.holderProduct (p := ⊤) (r := 2) (q := 2)).analyticAt_bilinear _).comp₂
      (hAa q hq.1.1.1) hmiddle
  have hGdata (q : PeriodOneHminusOne) (hq : q∈U) :
      ‖G q‖≤CA*(CR*(CB*CE)) ∧ (∀ j : ℤ, j≤0 → G q j=0) ∧
      ∀ n : ℕ+, G q (n : ℤ)=P.sourceAbelianCoordinateFormula (A q (n : ℤ)) n q := by
    have hEnorm : ‖P.sourceEtaSequence q‖≤CE := (hE _ hq.2.2 1 (by simp)).1
    have hAnorm := (hAb q hq.1.1.1).1
    have hRnorm := (hR q hq.1.1.2).1
    have hBnorm := (hB q hq.1.2).1
    refine ⟨?_,?_,?_⟩
    · exact (Coeff.norm_holderProduct_le _ _).trans
        (mul_le_mul hAnorm ((Coeff.norm_holderProduct_le _ _).trans
          (mul_le_mul hRnorm ((Coeff.norm_holderProduct_le _ _).trans
            (mul_le_mul hBnorm hEnorm (norm_nonneg _) hCB.le)) (norm_nonneg _) hCR.le))
          (norm_nonneg _) hCA.le)
    · intro j hj
      change A q j*(R q j*(B q j*P.sourceEtaSequence q j))=0
      rw [(hAb q hq.1.1.1).2 j hj,zero_mul]
    · intro n
      change A q (n : ℤ)*(R q (n : ℤ)*(B q (n : ℤ)*P.sourceEtaSequence q (n : ℤ)))=_
      rw [(hR q hq.1.1.2).2.2,(hB q hq.1.2).2.2]
      dsimp only [HillHminusPsiChart.sourceAbelianCoordinateFormula]
      ring
  obtain ⟨η,hη,hηU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  refine ⟨η,CA*(CR*(CB*CE))+1,G,hη,by positivity,hGa.mono hηU,?_,?_⟩
  · intro q hq
    exact ⟨(hGdata q (hηU hq)).1.trans (by linarith),(hGdata q (hηU hq)).2.1⟩
  · intro p hp n hw
    have hpU := hηU hp
    rw [(hGdata _ hpU).2.2,hAp p hpU.1.1.1 n]
    have hpP := hpU.2.1.1
    have hgap : hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0 := by
      intro hz
      exact hw (hillDirichletSheetRoot_eq_zero_of_halfLength_zero p.val p.property.1 p.property.2 n n.pos hz)
    exact P.sourceAbelianCoordinateFormula_sq_eq_original H p hpP hreal (houtside _ hpP.1) c hshift n hgap hw

end NLS.Articles.KdVKdV2Frequencies
