import NLS.Articles.KdVKdV2Frequencies.RoughSobolevAbelianCompactPacket
import NLS.KdV.HillRoughAbelianPacketSigns

/-! # Exact compact packet derivatives of ANY SAME physical positive map

One infinite sign selection fixes the supplied actual map throughout a
common complex rough ball. It precedes every Sobolev order and source.
The actual weighted derivatives retain the SAME eta and full symbol.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- ANY given actual positive rough map with original physical recovery
has exact, fixed-sign full-symbol compact derivative germs, ALL orders.
The supplied map is retained throughout the WHOLE smaller complex ball. -/
theorem exists_actual_positive_abelian_compact_germs
    (η : ℝ) (hη : 0<η) (Z : PeriodOneHminusOne → Coeff 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hZzero : ∀ q∈ball (0 : PeriodOneHminusOne) η, ∀ j : ℤ, j≤0 → Z q j=0)
    (hZphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
      Z (hillPhysicalHminusEmbedding p).val (n : ℤ)=
        hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
          (Real.sqrt (1+(n : ℝ)) : ℂ)) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ≤η ∧ ∃ P : HillHminusPsiChart,
      ∃ σ : PeriodOneHminusOne → Coeff ⊤, ∃ e : ℤ → Bool,
        AnalyticOnNhd ℂ σ (ball (0 : PeriodOneHminusOne) ρ) ∧
        (∀ p∈ball (0 : PeriodOneHminusOne) ρ, Z p=Coeff.signChange e (P.sourceAbelianSymbolPacket σ p)) ∧
        ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
          IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q) →
          periodOneSobolevImageInclusion t ht q∈ball (0 : PeriodOneHminusOne) ρ →
          ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
            ∃ M : ℝ, ∃ F H : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2,
              0≤M ∧ AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℂ H V ∧ ∀ p∈V,
                periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) ρ ∧ ‖H p‖≤M ∧
                (∀ n : ℤ, F p n=(Weight.sobolev t n : ℂ)*P.sourceEtaSequence (periodOneSobolevImageInclusion t ht p) n) ∧
                (∀ n : ℤ, H p n=(Weight.sobolev t n : ℂ)*Z (periodOneSobolevImageInclusion t ht p) n) ∧
                IsCompactOperator (fderiv ℂ H p-(Coeff.signChange e).comp
                  ((Coeff.holderProduct (q := 2) (σ (periodOneSobolevImageInclusion t ht p))).comp (fderiv ℂ F p))) := by
  obtain ⟨r,_C,P,σ,G,hr,_hC,hGa,hσa,hGeq,hGb,hGphys,hstrong⟩ :=
    exists_hillHminus_all_sobolev_abelian_compact_packet
  let ρ := min η r
  have hρ : 0<ρ := lt_min hη hr
  have hsubZ : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) η :=
    ball_subset_ball (min_le_left _ _)
  have hsubG : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) r :=
    ball_subset_ball (min_le_right _ _)
  obtain ⟨e,he⟩ := exists_constant_signChange_positive_rough_packet ρ hρ G Z
    (hGa.mono hsubG) (hZa.mono hsubZ) (fun q hq => (hGb q (hsubG hq)).2)
    (fun q hq => hZzero q (hsubZ hq))
    (fun p hp n hw => hGphys p (hsubG hp) n hw) (fun p hp n => hZphys p (hsubZ hp) n)
  refine ⟨ρ,hρ,min_le_left _ _,P,σ,e,hσa.mono hsubG,?_,?_⟩
  · intro p hp
    rw [he p hp,hGeq p (hsubG hp)]
  · intro t ht q hqr hq
    obtain ⟨U,hU,hqU,M,F,E,hM,hFa,hEa,hdata⟩ := hstrong t ht q hqr (hsubG hq)
    let A := fun p => (Coeff.holderProduct (q := 2) (σ (periodOneSobolevImageInclusion t ht p))).comp (fderiv ℂ F p)
    obtain ⟨V,hV,hqV,hVU,H,hHa,hHd⟩ := Coeff.exists_constant_sign_weighted_packet_germ
      (periodOneSobolevImageInclusion t ht) (ball (0 : PeriodOneHminusOne) ρ) isOpen_ball
      e Z G he U hU q hqU hq (fun n => (Weight.sobolev t n : ℂ)) M E hEa
      (fun p hp => (hdata p hp).2.1) (fun p hp => (hdata p hp).2.2.2.1) A
      (fun p hp => (hdata p hp).2.2.2.2)
    exact ⟨V,hV,hqV,M,F,H,hM,hFa.mono hVU,hHa,fun p hp =>
      ⟨(hHd p hp).1,(hHd p hp).2.1,(hdata p (hVU hp)).2.2.1,(hHd p hp).2.2⟩⟩

end NLS.Articles.KdVKdV2Frequencies
