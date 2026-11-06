import NLS.KdV.HillHminusAllSobolevEtaCharts
import NLS.KdV.HillHminusSobolevAbelianSymbols
import NLS.Articles.KdVKdV2Frequencies.RoughUniformActionAmplitudes
import NLS.KdV.HillHminusSourceAbelianSquare
import NLS.KdV.HillHminusSobolevAbelianCompact

/-! # Actual full Abelian packets with compact symbol derivatives

One actual Hill chart, full amplitude/midpoint/phase symbol and rough
packet precede all orders and eligible real sources. Each native complex
neighborhood retains the actual own-index eta and a compact derivative
remainder from differentiating the full symbol. Original physical squares
and off-sheet recovery remain attached to this SAME packet.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- The ACTUAL full physical squared Abelian packet has a compact symbol
derivative remainder at EVERY complex point of ALL native Sobolev germs.
No amplitude-only map or finite-support replacement is used. -/
theorem exists_hillHminus_all_sobolev_abelian_compact_packet :
    ∃ η C : ℝ, ∃ P : HillHminusPsiChart,
      ∃ σ : PeriodOneHminusOne → Coeff ⊤, ∃ G : PeriodOneHminusOne → Coeff 2,
      0<η ∧ 0<C ∧ AnalyticOnNhd ℂ G (ball (0 : PeriodOneHminusOne) η) ∧
      AnalyticOnNhd ℂ σ (ball (0 : PeriodOneHminusOne) η) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, G q=P.sourceAbelianSymbolPacket σ q) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, ‖G q‖≤C ∧ ∀ j : ℤ, j≤0 → G q j=0) ∧
      (∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
          (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)≠0 →
        (G (hillPhysicalHminusEmbedding p).val (n : ℤ))^2=
          (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos)^2/(1+(n : ℕ) : ℂ)) ∧
      ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q) →
        periodOneSobolevImageInclusion t ht q∈ball (0 : PeriodOneHminusOne) η →
        ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
          ∃ M : ℝ, ∃ F E : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2,
            0≤M ∧ AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℂ E V ∧ ∀ p∈V,
              periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) η ∧ ‖E p‖≤M ∧
              (∀ n : ℤ, F p n=(Weight.sobolev t n : ℂ)*
                P.sourceEtaSequence (periodOneSobolevImageInclusion t ht p) n) ∧
              (∀ n : ℤ, E p n=(Weight.sobolev t n : ℂ)*G (periodOneSobolevImageInclusion t ht p) n) ∧
              IsCompactOperator (fderiv ℂ E p-
                (Coeff.holderProduct (q := 2) (σ (periodOneSobolevImageInclusion t ht p))).comp (fderiv ℂ F p)) := by
  obtain ⟨P,c,_hc,hshift,h0B,hrealFixed,houtside,_hlabels,H,hSob⟩ :=
    exists_hillHminus_all_sobolev_eta_charts 0 (by intro n;simp)
  have hreal (q : PeriodOneHminusOne) (hq : q∈P.miura.domain) (hr : IsRealPeriodOneHminusOne q) :
      ∀ n : ℤ, P.miura.lift q (-n)=conj (P.miura.lift q n) :=
    (periodOneL2Conjugation_fixed_iff _).mp (hrealFixed q hq hr)
  obtain ⟨r,CA,A,hr,hCA,hAa,hAb,_hA0,hAp⟩ := exists_hillHminus_native_action_amplitude_symbol
  obtain ⟨Ur,hUr,h0Ur,_hUrP,CR,R,hCR,hRa,hR⟩ := P.exists_local_native_sourceNormalizedMidpoint H 0 h0B
  obtain ⟨Ub,hUb,h0Ub,_hUbP,CB,B,hCB,hBa,hB⟩ := P.exists_local_native_sourceNoncentralBeta_exp H 0 h0B
  obtain ⟨Ve,hVe,h0Ve,_hVeW,CE,hCE,_hEa,hE⟩ := H.gapWeighted_original_local_sequence (P.dirichletSource 0) h0B.2
  let Ue := P.sourceBetaDomain∩P.dirichletSource ⁻¹' Ve
  have hcont : ContinuousOn P.dirichletSource P.sourceBetaDomain :=
    P.analyticOnNhd_dirichletSource.continuousOn.mono inter_subset_left
  have hUe : IsOpen Ue := hcont.isOpen_inter_preimage P.sourceBetaDomain_open hVe
  let U := ball (0 : PeriodOneHminusOne) r∩Ur∩Ub∩Ue
  have hU : IsOpen U := ((isOpen_ball.inter hUr).inter hUb).inter hUe
  have h0U : (0 : PeriodOneHminusOne)∈U := ⟨⟨⟨mem_ball_self hr,h0Ur⟩,h0Ub⟩,h0B,h0Ve⟩
  let σ := fun q => Coeff.holderProduct (q := ⊤) (A q) (Coeff.holderProduct (q := ⊤) (R q) (B q))
  let K := CA*(CR*CB)
  have hK : 0≤K := by dsimp only [K];positivity
  have hσa : AnalyticOnNhd ℂ σ U := by
    intro q hq
    exact ((Coeff.holderProduct (p := ⊤) (r := ⊤) (q := ⊤)).analyticAt_bilinear _).comp₂
      (hAa q hq.1.1.1)
      (((Coeff.holderProduct (p := ⊤) (r := ⊤) (q := ⊤)).analyticAt_bilinear _).comp₂
        (hRa q hq.1.1.2) (hBa q hq.1.2))
  have hσb (q : PeriodOneHminusOne) (hq : q∈U) : ‖σ q‖≤K := by
    exact (Coeff.norm_holderProduct_le _ _).trans
      (mul_le_mul (hAb q hq.1.1.1).1
        ((Coeff.norm_holderProduct_le _ _).trans
          (mul_le_mul (hR q hq.1.1.2).1 (hB q hq.1.2).1 (norm_nonneg _) hCR.le))
        (norm_nonneg _) hCA.le)
  let G := P.sourceAbelianSymbolPacket σ
  have hGa : AnalyticOnNhd ℂ G U := fun q hq =>
    P.analyticOnNhd_sourceAbelianSymbolPacket H σ U hσa q ⟨hq.2.1,hq⟩
  have hGdata (q : PeriodOneHminusOne) (hq : q∈U) :
      ‖G q‖≤K*CE ∧ (∀ j : ℤ, j≤0 → G q j=0) ∧
      ∀ n : ℕ+, G q (n : ℤ)=P.sourceAbelianCoordinateFormula (A q (n : ℤ)) n q := by
    have hn : ‖P.sourceEtaSequence q‖≤CE := (hE _ hq.2.2 1 (by simp)).1
    refine ⟨(Coeff.norm_holderProduct_le _ _).trans (mul_le_mul (hσb q hq) hn (norm_nonneg _) hK),?_,?_⟩
    · intro j hj
      change (A q j*(R q j*B q j))*P.sourceEtaSequence q j=0
      rw [(hAb q hq.1.1.1).2 j hj,zero_mul,zero_mul]
    · intro n
      change (A q (n : ℤ)*(R q (n : ℤ)*B q (n : ℤ)))*P.sourceEtaSequence q (n : ℤ)=_
      rw [(hR q hq.1.1.2).2.2,(hB q hq.1.2).2.2]
      dsimp only [HillHminusPsiChart.sourceAbelianCoordinateFormula]
      ring
  obtain ⟨η,hη,hηU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  refine ⟨η,K*CE+1,P,σ,G,hη,by positivity,hGa.mono hηU,hσa.mono hηU,
    (fun _ _ => rfl),?_,?_,?_⟩
  · intro q hq
    exact ⟨(hGdata q (hηU hq)).1.trans (by linarith),(hGdata q (hηU hq)).2.1⟩
  · intro p hp n hw
    have hpU := hηU hp
    rw [(hGdata _ hpU).2.2,hAp p hpU.1.1.1 n]
    have hgap : hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0 := by
      intro hz
      exact hw (hillDirichletSheetRoot_eq_zero_of_halfLength_zero p.val p.property.1 p.property.2 n n.pos hz)
    exact P.sourceAbelianCoordinateFormula_sq_eq_original H p hpU.2.1.1 hreal
      (houtside _ hpU.2.1.1.1) c hshift n hgap hw
  · intro t ht q hqr hq
    have hqU := hηU hq
    have heta := hSob t ht q hqr hqU.2.1.1.1
    obtain ⟨V,hV,hqV,M,F,E,hM,hFa,hEa,hdata⟩ := P.exists_sobolev_abelian_symbol_packet_compact_germ σ
      (ball 0 η) isOpen_ball (hσa.mono hηU) K hK (fun p hp => hσb p (hηU hp))
      t ht q hq heta
    exact ⟨V,hV,hqV,M,F,E,hM,hFa,hEa,fun p hp => ⟨(hdata p hp).1.2,(hdata p hp).2⟩⟩

end NLS.Articles.KdVKdV2Frequencies
