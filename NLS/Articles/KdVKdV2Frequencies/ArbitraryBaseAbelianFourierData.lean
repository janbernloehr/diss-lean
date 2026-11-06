import NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierData
import NLS.KdV.HillHminusArbitraryBaseAmplitudeSymbol
import NLS.KdV.HillHminusMidpointLowerBound
import NLS.KdV.HillHminusNoncentralPhaseReciprocal
import NLS.KdV.HillHminusRetainedMiuraEtaChart
import NLS.KdV.HillHminusSourceAbelianSquare
import NLS.KdV.HillHminusSobolevAbelianSymbols

/-! # Actual full Abelian packets at every real rough base

The chart, original roots and native Miura lift witnesses are retained.
Every complex source in one rough ball has the literal full amplitude,
normalized midpoint and noncentral phase factors, including low modes.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- Actual full packet data needed for the mean-zero Jacobian argument. -/
structure RoughAbelianFourierDataAt (q0 : PeriodOneHminusOne) where
  radius : ℝ
  radius_pos : 0<radius
  chart : HillHminusPsiChart
  roots : SourceLemma12_12Data (by norm_num) (by norm_num)
    chart.family.originalDomain chart.family.domain chart.family.roots
  native_lifts : HasAllNativeMiuraGerms chart
  real_lift : ∀ q∈chart.miura.domain, IsRealPeriodOneHminusOne q →
    periodOneL2Conjugation (chart.miura.lift q)=chart.miura.lift q
  source_domain : ball q0 radius⊆chart.sourceBetaDomain
  amplitude : PeriodOneHminusOne → Coeff ⊤
  amplitude_analytic : AnalyticOnNhd ℂ amplitude (ball q0 radius)
  amplitude_physical : ∀ p : RealPeriodOneHillPotential,
    (hillPhysicalHminusEmbedding p).val∈ball q0 radius → ∀ n : ℕ+,
      amplitude (hillPhysicalHminusEmbedding p).val (n : ℤ)=
        (Real.sqrt (1+(n : ℝ)) : ℂ)*
          hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ)
  symbol : PeriodOneHminusOne → Coeff ⊤
  reciprocal : PeriodOneHminusOne → Coeff ⊤
  packet : PeriodOneHminusOne → Coeff 2
  symbol_upper : ℝ
  symbol_lower : ℝ
  packet_bound : ℝ
  upper_pos : 0<symbol_upper
  lower_pos : 0<symbol_lower
  packet_bound_pos : 0<packet_bound
  symbol_analytic : AnalyticOnNhd ℂ symbol (ball q0 radius)
  reciprocal_analytic : AnalyticOnNhd ℂ reciprocal (ball q0 radius)
  packet_analytic : AnalyticOnNhd ℂ packet (ball q0 radius)
  symbol_data : ∀ q∈ball q0 radius,
    ‖symbol q‖≤symbol_upper ∧ ‖reciprocal q‖≤symbol_lower⁻¹ ∧
    (∀ j : ℤ, j≤0 → symbol q j=0 ∧ reciprocal q j=0) ∧ ∀ n : ℕ+,
      symbol q (n : ℤ)=amplitude q (n : ℤ)*
        (chart.sourceNormalizedMidpoint n q*exp (I*chart.sourceNoncentralBeta n q)) ∧
      symbol_lower≤‖symbol q (n : ℤ)‖ ∧
      reciprocal q (n : ℤ)=(symbol q (n : ℤ))⁻¹ ∧ symbol q (n : ℤ)*reciprocal q (n : ℤ)=1
  packet_data : ∀ q∈ball q0 radius,
    packet q=chart.sourceAbelianSymbolPacket symbol q ∧ ‖packet q‖≤packet_bound ∧
    ∀ j : ℤ, j≤0 → packet q j=0
  packet_coordinates : ∀ q∈ball q0 radius, ∀ n : ℕ+,
    packet q (n : ℤ)=chart.sourceAbelianCoordinateFormula (amplitude q (n : ℤ)) n q
  physical_squares : ∀ p : RealPeriodOneHillPotential,
    (hillPhysicalHminusEmbedding p).val∈ball q0 radius → ∀ n : ℕ+,
    hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
      (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)≠0 →
    (packet (hillPhysicalHminusEmbedding p).val (n : ℤ))^2=
      (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos)^2/(1+(n : ℕ) : ℂ)

/-- The ACTUAL full symbol is uniformly nonzero on positive slots on ONE
complex rough ball. ONE chart, original roots and actual lift witnesses
precede all indices, Sobolev orders and eligible real sources. -/
theorem nonempty_roughAbelianFourierDataAt
    (q0 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) :
    Nonempty (RoughAbelianFourierDataAt q0) := by
  obtain ⟨P,c,_hc,hshift,h0B,hrealFixed,houtside,_hlabels,H,hstrong⟩ :=
    exists_hillHminus_retained_Miura_eta_chart q0 hr0
  have hreal (q : PeriodOneHminusOne) (hq : q∈P.miura.domain) (hr : IsRealPeriodOneHminusOne q) :
      ∀ n : ℤ, P.miura.lift q (-n)=conj (P.miura.lift q n) :=
    (periodOneL2Conjugation_fixed_iff _).mp (hrealFixed q hq hr)
  obtain ⟨r,aA,CA,A,_Ai,hr,haA,hCA,hAa,_hAia,hAd,hAp⟩ :=
    exists_hillHminus_arbitrary_base_native_amplitude_reciprocal q0 hr0
  obtain ⟨Ur,hUr,h0Ur,_hUrP,a,CR,R,_Ri,ha,hCR,hRa,_hRia,hRd⟩ :=
    P.exists_local_native_sourceNormalizedMidpoint_reciprocal H q0 h0B (hrealFixed q0 h0B.1.1 hr0)
  obtain ⟨Ub,hUb,h0Ub,_hUbP,CB,B,_Bi,hCB,hBa,_hBia,hBd⟩ :=
    P.exists_local_native_sourceNoncentralPhase_reciprocal H q0 h0B
  obtain ⟨Ve,hVe,h0Ve,_hVeW,CE,hCE,_hEa,hE⟩ := H.gapWeighted_original_local_sequence (P.dirichletSource q0) h0B.2
  let Ue := P.sourceBetaDomain∩P.dirichletSource ⁻¹' Ve
  have hcont : ContinuousOn P.dirichletSource P.sourceBetaDomain :=
    P.analyticOnNhd_dirichletSource.continuousOn.mono inter_subset_left
  have hUe : IsOpen Ue := hcont.isOpen_inter_preimage P.sourceBetaDomain_open hVe
  let U := ball q0 r∩Ur∩Ub∩Ue
  have hU : IsOpen U := ((isOpen_ball.inter hUr).inter hUb).inter hUe
  have h0U : q0∈U := ⟨⟨⟨mem_ball_self hr,h0Ur⟩,h0Ub⟩,h0B,h0Ve⟩
  let σ := fun q => Coeff.holderProduct (q := ⊤) (A q) (Coeff.holderProduct (q := ⊤) (R q) (B q))
  let K := CA*(CR*CB)
  let b := aA*(a*CB⁻¹)
  have hK : 0<K := by dsimp only [K];positivity
  have hb : 0<b := by dsimp only [b];positivity
  have hσa : AnalyticOnNhd ℂ σ U := by
    intro q hq
    exact ((Coeff.holderProduct (p := ⊤) (r := ⊤) (q := ⊤)).analyticAt_bilinear _).comp₂
      (hAa q hq.1.1.1)
      (((Coeff.holderProduct (p := ⊤) (r := ⊤) (q := ⊤)).analyticAt_bilinear _).comp₂
        (hRa q hq.1.1.2) (hBa q hq.1.2))
  have hσb (q : PeriodOneHminusOne) (hq : q∈U) : ‖σ q‖≤K :=
    (Coeff.norm_holderProduct_le _ _).trans
      (mul_le_mul (hAd q hq.1.1.1).1
        ((Coeff.norm_holderProduct_le _ _).trans
          (mul_le_mul (hRd q hq.1.1.2).1 (hBd q hq.1.2).1 (norm_nonneg _) hCR.le))
        (norm_nonneg _) hCA.le)
  have hσl (q : PeriodOneHminusOne) (hq : q∈U) (n : ℕ+) : b≤‖σ q (n : ℤ)‖ := by
    change aA*(a*CB⁻¹)≤‖A q (n : ℤ)*(R q (n : ℤ)*B q (n : ℤ))‖
    rw [norm_mul,norm_mul]
    exact mul_le_mul ((hAd q hq.1.1.1).2.2.2 n).1
      (mul_le_mul ((hRd q hq.1.1.2).2.2.2 n).2.1 ((hBd q hq.1.2).2.2.2 n).2.2.1
        (by positivity) (norm_nonneg _)) (by positivity) (norm_nonneg _)
  obtain ⟨T,hTa,hTd⟩ := Coeff.exists_positive_analytic_reciprocal U hU σ hσa b hb hσl
  let G := P.sourceAbelianSymbolPacket σ
  have hGa : AnalyticOnNhd ℂ G U := fun q hq =>
    P.analyticOnNhd_sourceAbelianSymbolPacket H σ U hσa q ⟨hq.2.1,hq⟩
  have hGdata (q : PeriodOneHminusOne) (hq : q∈U) :
      ‖G q‖≤K*CE ∧ (∀ j : ℤ, j≤0 → G q j=0) ∧
      ∀ n : ℕ+, G q (n : ℤ)=P.sourceAbelianCoordinateFormula (A q (n : ℤ)) n q := by
    have hn : ‖P.sourceEtaSequence q‖≤CE := (hE _ hq.2.2 1 (by simp)).1
    refine ⟨(Coeff.norm_holderProduct_le _ _).trans (mul_le_mul (hσb q hq) hn (norm_nonneg _) hK.le),?_,?_⟩
    · intro j hj
      change (A q j*(R q j*B q j))*P.sourceEtaSequence q j=0
      rw [((hAd q hq.1.1.1).2.2.1 j hj).1,zero_mul,zero_mul]
    · intro n
      change (A q (n : ℤ)*(R q (n : ℤ)*B q (n : ℤ)))*P.sourceEtaSequence q (n : ℤ)=_
      rw [((hRd q hq.1.1.2).2.2.2 n).1,((hBd q hq.1.2).2.2.2 n).1]
      dsimp only [HillHminusPsiChart.sourceAbelianCoordinateFormula,HillHminusPsiChart.sourceNormalizedMidpoint]
      ring
  obtain ⟨η,hη,hηU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  refine ⟨{
    radius := η
    radius_pos := hη
    chart := P
    roots := H
    native_lifts := hstrong
    real_lift := hrealFixed
    source_domain := fun q hq => (hηU hq).2.1
    amplitude := A
    amplitude_analytic := hAa.mono (fun q hq => (hηU hq).1.1.1)
    amplitude_physical := fun p hp n => hAp p (hηU hp).1.1.1 n
    symbol := σ
    reciprocal := T
    packet := G
    symbol_upper := K
    symbol_lower := b
    packet_bound := K*CE+1
    upper_pos := hK
    lower_pos := hb
    packet_bound_pos := by positivity
    symbol_analytic := hσa.mono hηU
    reciprocal_analytic := hTa.mono hηU
    packet_analytic := hGa.mono hηU
    symbol_data := ?_
    packet_data := ?_
    packet_coordinates := fun q hq n => (hGdata q (hηU hq)).2.2 n
    physical_squares := ?_ }⟩
  · intro q hq
    have hqU := hηU hq
    refine ⟨hσb q hqU,(hTd q hqU).1,?_,?_⟩
    · intro j hj
      exact ⟨by change A q j*(R q j*B q j)=0;rw [((hAd q hqU.1.1.1).2.2.1 j hj).1,zero_mul],(hTd q hqU).2.1 j hj⟩
    · intro n
      refine ⟨?_,hσl q hqU n,(hTd q hqU).2.2 n⟩
      change A q (n : ℤ)*(R q (n : ℤ)*B q (n : ℤ))=_
      rw [((hRd q hqU.1.1.2).2.2.2 n).1,((hBd q hqU.1.2).2.2.2 n).1]
  · intro q hq
    exact ⟨rfl,(hGdata q (hηU hq)).1.trans (by linarith),(hGdata q (hηU hq)).2.1⟩
  · intro p hp n hw
    have hpU := hηU hp
    change (G (hillOriginalHminusSource p.val) (n : ℤ))^2 = _
    rw [(hGdata (hillOriginalHminusSource p.val) hpU).2.2,hAp p hpU.1.1.1 n]
    have hgap : hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0 := by
      intro hz
      exact hw (hillDirichletSheetRoot_eq_zero_of_halfLength_zero p.val p.property.1 p.property.2 n n.pos hz)
    exact P.sourceAbelianCoordinateFormula_sq_eq_original H p hpU.2.1.1 hreal
      (houtside _ hpU.2.1.1.1) c hshift n hgap hw

end NLS.Articles.KdVKdV2Frequencies
