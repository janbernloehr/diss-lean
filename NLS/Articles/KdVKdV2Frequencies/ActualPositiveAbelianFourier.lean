import NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierGerms
import NLS.KdV.HillRoughAbelianPacketSigns

/-! # The full Fourier principal of ANY SAME actual positive coordinate map -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- Exact full positive principal, retaining the SAME fixed physical signs. -/
def actualPositiveFourierPrincipal (D : RoughAbelianFourierData) (e : ℤ → Bool)
    (t : ℝ) (ht : 0≤t) (p : WeightedCoeff (Weight.sobolev (t-1)) 2) :
    WeightedCoeff (Weight.sobolev (t-1)) 2 →L[ℂ] Coeff 2 :=
  (Coeff.signChange e).comp (D.chart.nativeAbelianFourierPrincipal D.symbol t ht p)

/-- A genuine complex native germ of the GIVEN positive coordinate map,
with its actual full Fourier principal at every physically real point. -/
def PositiveAbelianFourierGermAt (ρ : ℝ) (D : RoughAbelianFourierData) (e : ℤ → Bool)
    (Y : PeriodOneHminusOne → Coeff 2) (t : ℝ) (ht : 0≤t)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2) : Prop :=
  ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
    ∃ M : ℝ, ∃ H : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2,
      0≤M ∧ AnalyticOnNhd ℂ H V ∧ ∀ p∈V,
        periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) ρ ∧ ‖H p‖≤M ∧
        (∀ n : ℤ, H p n=(Weight.sobolev t n : ℂ)*Y (periodOneSobolevImageInclusion t ht p) n) ∧
        (IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht p) →
          IsCompactOperator (fderiv ℂ H p-actualPositiveFourierPrincipal D e t ht p))

private theorem sign_weighted_real_packet_germ
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    (L : E →L[ℂ] P) (U : Set P) (hU : IsOpen U)
    (e : ℤ → Bool) (Y G : P → Coeff 2)
    (he : ∀ p∈U, Y p=Coeff.signChange e (G p))
    (V : Set E) (hV : IsOpen V) (q : E) (hqV : q∈V) (hqU : L q∈U)
    (w : ℤ → ℂ) (M : ℝ) (F : E → Coeff 2)
    (hFa : AnalyticOnNhd ℂ F V) (hFb : ∀ p∈V, ‖F p‖≤M)
    (hcoeff : ∀ p∈V, ∀ n : ℤ, F p n=w n*G (L p) n)
    (R : E → Prop) (A : E → E →L[ℂ] Coeff 2)
    (hc : ∀ p∈V, R p → IsCompactOperator (fderiv ℂ F p-A p)) :
    ∃ W : Set E, IsOpen W ∧ q∈W ∧ ∃ H : E → Coeff 2,
      AnalyticOnNhd ℂ H W ∧ ∀ p∈W,
        L p∈U ∧ ‖H p‖≤M ∧ (∀ n : ℤ, H p n=w n*Y (L p) n) ∧
        (R p → IsCompactOperator (fderiv ℂ H p-(Coeff.signChange e).comp (A p))) := by
  let W := V∩L ⁻¹' U
  let H := fun p => Coeff.signChange e (F p)
  refine ⟨W,hV.inter (hU.preimage L.continuous),⟨hqV,hqU⟩,H,?_,?_⟩
  · intro p hp
    exact ((Coeff.signChange e).analyticAt _).comp (hFa p hp.1)
  · intro p hp
    refine ⟨hp.2,?_,?_,?_⟩
    · simpa only [H,Coeff.norm_signChange] using hFb p hp.1
    · intro n
      rw [he _ hp.2]
      exact Coeff.signChange_weighted_packet e F (fun p => G (L p)) w p (hcoeff p hp.1) n
    · intro hpr
      exact Coeff.isCompactOperator_fderiv_signChange_sub e F p (hFa p hp.1).differentiableAt _ (hc p hp.1 hpr)

/-- For ANY supplied actual physical positive map, ONE smaller rough ball
and ONE infinite physical sign selection precede ALL orders and bases.
The ACTUAL chart, roots, full-symbol lower bounds and lift witnesses of D
are retained in its exact compact Fourier derivative comparison. -/
theorem exists_actual_positive_abelian_fourier_germs
    (D : RoughAbelianFourierData) (η : ℝ) (hη : 0<η) (Y : PeriodOneHminusOne → Coeff 2)
    (hYa : AnalyticOnNhd ℂ Y (ball (0 : PeriodOneHminusOne) η))
    (hYzero : ∀ q∈ball (0 : PeriodOneHminusOne) η, ∀ j : ℤ, j≤0 → Y q j=0)
    (hYphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
      Y (hillPhysicalHminusEmbedding p).val (n : ℤ)=
        hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/(Real.sqrt (1+(n : ℝ)) : ℂ)) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ≤η ∧ ρ≤D.radius ∧ ∃ e : ℤ → Bool,
      (∀ p∈ball (0 : PeriodOneHminusOne) ρ, Y p=Coeff.signChange e (D.packet p)) ∧
      ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q) →
        periodOneSobolevImageInclusion t ht q∈ball (0 : PeriodOneHminusOne) ρ →
        PositiveAbelianFourierGermAt ρ D e Y t ht q := by
  let ρ := min η D.radius
  have hρ : 0<ρ := lt_min hη D.radius_pos
  have hsubY : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) η :=
    ball_subset_ball (min_le_left _ _)
  have hsubD : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) D.radius :=
    ball_subset_ball (min_le_right _ _)
  obtain ⟨e,he⟩ := exists_constant_signChange_positive_rough_packet ρ hρ D.packet Y
    (D.packet_analytic.mono hsubD) (hYa.mono hsubY)
    (fun q hq => (D.packet_data q (hsubD hq)).2.2) (fun q hq => hYzero q (hsubY hq))
    (fun p hp n hw => D.physical_squares p (hsubD hp) n hw) (fun p hp n => hYphys p (hsubY hp) n)
  refine ⟨ρ,hρ,min_le_left _ _,min_le_right _ _,e,he,?_⟩
  intro t ht q hqr hq
  obtain ⟨V,hV,hqV,M,E,hM,hEa,hdata⟩ := D.exists_native_packet_fourier_germ t ht q hqr (hsubD hq)
  obtain ⟨W,hW,hqW,H,hHa,hHd⟩ := sign_weighted_real_packet_germ
    (periodOneSobolevImageInclusion t ht) (ball (0 : PeriodOneHminusOne) ρ) isOpen_ball
    e Y D.packet he V hV q hqV hq (fun n => (Weight.sobolev t n : ℂ)) M E hEa
    (fun p hp => (hdata p hp).2.1) (fun p hp => (hdata p hp).2.2.1)
    (fun p => IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht p))
    (D.chart.nativeAbelianFourierPrincipal D.symbol t ht) (fun p hp => (hdata p hp).2.2.2)
  exact ⟨W,hW,hqW,M,H,hM,hHa,hHd⟩

end NLS.Articles.KdVKdV2Frequencies
