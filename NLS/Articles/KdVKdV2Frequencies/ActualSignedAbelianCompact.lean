import NLS.Articles.KdVKdV2Frequencies.ActualPositiveAbelianCompact
import NLS.Articles.KdVKdV2Frequencies.NativeRoughAbelianPacket
import NLS.KdV.HillAbelianSignedPhysicalRecovery
import NLS.KdV.HillRoughPhysicalUniqueness
import NLS.SequenceSpaces.SobolevSignedCompactGerm

/-! # Compact full signed derivative formulas for the SAME actual map

Original physical recovery fixes the supplied weak signed map. ONE actual
chart, full symbol and infinite constant signs precede all Sobolev orders.
Every stronger signed germ includes EXACTLY to that supplied map and has
its actual eta/symbol principal derivative plus a compact remainder.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- The actual positive principal derivative, retaining the fixed physical
coordinate signs, full complex symbol and native weighted eta derivative. -/
def actualPositiveEtaPrincipal (σ : PeriodOneHminusOne → Coeff ⊤) (e : ℤ → Bool)
    (t : ℝ) (ht : 0≤t) (F : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2)
    (p : WeightedCoeff (Weight.sobolev (t-1)) 2) :
    WeightedCoeff (Weight.sobolev (t-1)) 2 →L[ℂ] Coeff 2 :=
  (Coeff.signChange e).comp ((Coeff.holderProduct (q := 2)
    (σ (periodOneSobolevImageInclusion t ht p))).comp (fderiv ℂ F p))

/-- The exact full signed eta principal operator in its native target. -/
def actualSignedEtaPrincipal (σ : PeriodOneHminusOne → Coeff ⊤) (e : ℤ → Bool)
    (t : ℝ) (ht : 0≤t) (F : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2)
    (p : WeightedCoeff (Weight.sobolev (t-1)) 2) :
    WeightedCoeff (Weight.sobolev (t-1)) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (t-1/2)) 2 :=
  WeightedCoeff.nativeSignedPrincipal (Weight.sobolev (t-1)) (Weight.sobolev (t-1/2))
    (Weight.sobolev_neg (t-1)) (actualPositiveEtaPrincipal σ e t ht F p)
    (actualPositiveEtaPrincipal σ e t ht F
      (WeightedCoeff.conjugateReflection (Weight.sobolev (t-1)) (Weight.sobolev_neg (t-1)) p))

/-- The actual full signed compact derivative assertion at one native
base, on a conjugation-invariant OPEN COMPLEX neighborhood. -/
def SignedAbelianCompactGermAt (ρ : ℝ)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (P : HillHminusPsiChart) (σ : PeriodOneHminusOne → Coeff ⊤) (e : ℤ → Bool)
    (t : ℝ) (ht : 0≤t) (q : WeightedCoeff (Weight.sobolev (t-1)) 2) : Prop :=
  ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
          (∀ p∈V, WeightedCoeff.conjugateReflection (Weight.sobolev (t-1)) (Weight.sobolev_neg (t-1)) p∈V) ∧
          ∃ C : ℝ, ∃ F : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2,
            ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
              0≤C ∧ AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
                periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) ρ ∧ ‖g p‖≤C ∧
                (∀ n : ℤ, F p n=(Weight.sobolev t n : ℂ)*P.sourceEtaSequence (periodOneSobolevImageInclusion t ht p) n) ∧
                WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (g p)=
                  Z (periodOneSobolevImageInclusion t ht p) ∧
                IsCompactOperator (fderiv ℂ g p-actualSignedEtaPrincipal σ e t ht F p)

/-- A precise full signed compact derivative property of a GIVEN actual
map, on ONE smaller complex rough ball before ALL orders and real bases. -/
def HasSignedAbelianCompactGerms (η : ℝ)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2) : Prop :=
  ∃ ρ : ℝ, 0<ρ ∧ ρ≤η ∧ ∃ P : HillHminusPsiChart,
    ∃ σ : PeriodOneHminusOne → Coeff ⊤, ∃ e : ℤ → Bool,
      AnalyticOnNhd ℂ σ (ball (0 : PeriodOneHminusOne) ρ) ∧
      ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q) →
        periodOneSobolevImageInclusion t ht q∈ball (0 : PeriodOneHminusOne) ρ →
        SignedAbelianCompactGermAt ρ Z P σ e t ht q

private theorem attach_auxiliary_compact_germ
    {E G P Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    (L : E →L[ℂ] P) (I : G → Y) (T Z : P → Y) (D : Set P) (heq : EqOn T Z D)
    (J : E → E) (R : P → ℤ → ℂ) (w : ℤ → ℂ)
    (U : Set E) (F : E → Coeff 2) (hFa : AnalyticOnNhd ℂ F U)
    (hcoeff : ∀ p∈U, ∀ n : ℤ, F p n=w n*R (L p) n)
    (A : (E → Coeff 2) → E → E →L[ℂ] G) (q : E)
    (hgerm : ∃ V : Set E, IsOpen V ∧ q∈V ∧ V⊆U ∧ (∀ p∈V, J p∈V) ∧
      ∃ C : ℝ, ∃ g : E → G, 0≤C ∧ AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
        L p∈D ∧ ‖g p‖≤C ∧ I (g p)=T (L p) ∧ IsCompactOperator (fderiv ℂ g p-A F p)) :
    ∃ V : Set E, IsOpen V ∧ q∈V ∧ (∀ p∈V, J p∈V) ∧
      ∃ C : ℝ, ∃ F' : E → Coeff 2, ∃ g : E → G,
        0≤C ∧ AnalyticOnNhd ℂ F' V ∧ AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
          L p∈D ∧ ‖g p‖≤C ∧ (∀ n : ℤ, F' p n=w n*R (L p) n) ∧
          I (g p)=Z (L p) ∧ IsCompactOperator (fderiv ℂ g p-A F' p) := by
  obtain ⟨V,hV,hqV,hVU,hJ,C,g,hC,hga,hd⟩ := hgerm
  refine ⟨V,hV,hqV,hJ,C,F,g,hC,hFa.mono hVU,hga,?_⟩
  intro p hp
  exact ⟨(hd p hp).1,(hd p hp).2.1,hcoeff p (hVU hp),
    ((hd p hp).2.2.1).trans (heq (hd p hp).1),(hd p hp).2.2.2⟩

private theorem signed_compact_germ_of_positive
    (ρ : ℝ) (Y : PeriodOneHminusOne → Coeff 2)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hTZ : EqOn (WeightedCoeff.signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2)) Y)
      Z (ball (0 : PeriodOneHminusOne) ρ))
    (P : HillHminusPsiChart) (σ : PeriodOneHminusOne → Coeff ⊤) (e : ℤ → Bool)
    (t : ℝ) (ht : 0≤t) (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q))
    (U : Set (WeightedCoeff (Weight.sobolev (t-1)) 2)) (hU : IsOpen U) (hqU : q∈U)
    (M : ℝ) (hM : 0≤M) (F H : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2)
    (hFa : AnalyticOnNhd ℂ F U) (hHa : AnalyticOnNhd ℂ H U)
    (hdata : ∀ p∈U, periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) ρ ∧ ‖H p‖≤M ∧
      (∀ n : ℤ, F p n=(Weight.sobolev t n : ℂ)*P.sourceEtaSequence (periodOneSobolevImageInclusion t ht p) n) ∧
      (∀ n : ℤ, H p n=(Weight.sobolev t n : ℂ)*Y (periodOneSobolevImageInclusion t ht p) n) ∧
      IsCompactOperator (fderiv ℂ H p-actualPositiveEtaPrincipal σ e t ht F p)) :
    SignedAbelianCompactGermAt ρ Z P σ e t ht q := by
  apply attach_auxiliary_compact_germ (periodOneSobolevImageInclusion t ht)
    (WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2))
    (WeightedCoeff.signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2)) Y) Z
    (ball (0 : PeriodOneHminusOne) ρ) hTZ
    (WeightedCoeff.conjugateReflection (Weight.sobolev (t-1)) (Weight.sobolev_neg (t-1)))
    (fun p n => P.sourceEtaSequence p n) (fun n => (Weight.sobolev t n : ℂ)) U F
    hFa (fun p hp => (hdata p hp).2.2.1) (actualSignedEtaPrincipal σ e t ht) q
  exact exists_sobolev_signedTargetLift_compact_germ t ht Y ρ q hqr U hU hqU M hM H hHa
    (fun p hp => ⟨(hdata p hp).1,(hdata p hp).2.1,(hdata p hp).2.2.2.1⟩)
    (actualPositiveEtaPrincipal σ e t ht F) (fun p hp => (hdata p hp).2.2.2.2)

/-- ANY GIVEN actual signed physical map has compact full signed native
eta/symbol derivative germs. Original physical recovery fixes the SAME
map on the whole common complex ball, including all closed/low gaps. -/
theorem exists_actual_signed_abelian_compact_germs
    (η : ℝ) (hη : 0<η)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hZphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) :
    HasSignedAbelianCompactGerms η Z := by
  obtain ⟨r,_CY,Y,hr,_hCY,hYa,_hY0,hYb,hYphys⟩ := exists_hillHminus_native_normalized_abelian_packet
  let r0 := min η r
  have hr0 : 0<r0 := lt_min hη hr
  have hsub0Y : ball (0 : PeriodOneHminusOne) r0⊆ball (0 : PeriodOneHminusOne) r :=
    ball_subset_ball (min_le_right _ _)
  obtain ⟨ρ,hρ,hρ0,P,σ,e,hσa,_heq,hstrong⟩ := exists_actual_positive_abelian_compact_germs
    r0 hr0 Y (hYa.mono hsub0Y) (fun p hp => (hYb p (hsub0Y hp)).2)
    (fun p hp n => hYphys p (hsub0Y hp) n)
  have hρη : ρ≤η := hρ0.trans (min_le_left _ _)
  have hsubZ : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) η :=
    ball_subset_ball hρη
  have hsubY : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) r :=
    ball_subset_ball (hρ0.trans (min_le_right _ _))
  let T := WeightedCoeff.signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2)) Y
  have hTa : AnalyticOnNhd ℂ T (ball (0 : PeriodOneHminusOne) ρ) := by
    intro p hp
    apply WeightedCoeff.analyticOnNhd_signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2))
      (Weight.sobolev_neg (-1)) Y (ball (0 : PeriodOneHminusOne) r) hYa p
    refine ⟨hsubY hp,?_⟩
    simpa only [mem_preimage,mem_ball_zero_iff,WeightedCoeff.norm_conjugateReflection] using hsubY hp
  have hTZ : EqOn T Z (ball (0 : PeriodOneHminusOne) ρ) := by
    apply eqOn_weighted_rough_ball_of_physical_eq _ ρ hρ T Z hTa (hZa.mono hsubZ)
    intro p hp
    apply Subtype.ext
    funext j
    exact (hillAbelian_signedTargetLift_physical r Y (fun q hq => (hYb q hq).2) hYphys p (hsubY hp) j).trans
      (hZphys p (hsubZ hp) j).symm
  refine ⟨ρ,hρ,hρη,P,σ,e,hσa,?_⟩
  intro t ht q hqr hq
  obtain ⟨U,hU,hqU,M,F,H,hM,hFa,hHa,hdata⟩ := hstrong t ht q hqr hq
  exact signed_compact_germ_of_positive ρ Y Z hTZ P σ e t ht q hqr U hU hqU M hM F H hFa hHa hdata

end NLS.Articles.KdVKdV2Frequencies
