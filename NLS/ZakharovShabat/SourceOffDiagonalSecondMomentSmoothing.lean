import NLS.ZakharovShabat.SourceSobolevSecondMomentPacket
import NLS.ZakharovShabat.SourceRefinedCubicNormBounds
import NLS.ZakharovShabat.SourceSobolevSquaredGapBounds
import NLS.SequenceSpaces.NegativeWeightReciprocalColumns
import NLS.ZakharovShabat.SourceOffDiagonalSecondMomentBounds

/-! The actual off-diagonal moment sum admits a strictly stronger
negative weighted ell1 target at every intermediate source order.
All estimates hold on full complex source neighborhoods. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem SourceAbelianMomentAtlas.exists_analytic_negativeWeightedOffDiagonalSecondMomentPacket
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (a b σ t : ℝ) (hb1 : b<1) (hσ : 0<σ) (hσb : σ<b)
    (ht : 0<t) (hat : 2*t=1-a) (horder : 1≤σ+t+(1-a))
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2⊆V) :
    let w := sourceSobolevSpectralWeight t ht.le
    let L := normalizedWeightedSourceCLM (p := 2) w
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ realTypeSourceLocus 2⊆U ∧ U⊆L ⁻¹' (A.domain∩V) ∧
      AnalyticOnNhd ℂ (fun φ => A.negativeWeightedOffDiagonalSecondMomentPacket b (L φ)) U ∧
      (∀ φ∈U, ∀ n : ℤ, A.negativeWeightedOffDiagonalSecondMomentPacket b (L φ) n=
        (Weight.sobolev (-b) n : ℂ)*(if 0<n then A.weightedSecondMomentSum n (L φ)-(n : ℂ)*(A.moment n n 2 (L φ)-A.moment n (-n) 2 (L φ)) else 0)) ∧
      ∀ φ∈U, ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ∈T ∧ T⊆U ∧
        ∃ K : ℝ, 0≤K ∧ ∀ ψ∈T, ‖A.negativeWeightedOffDiagonalSecondMomentPacket b (L ψ)‖≤K := by
  intro w L
  obtain ⟨Ub,hUb,hrealUb,hUbV,_hsumb,hbounds⟩ :=
    A.exists_negativeWeightedOffDiagonalSecondMoment_localBounds a b σ t hb1 hσ hσb ht hat horder hs hV hrealV
  obtain ⟨Us,hUs,_hUsc,hrealUs,_hUsV,hsum,ha,_hconv,_hlocalUs⟩ :=
    A.exists_analytic_weightedSecondMomentSum hs hV hrealV
  let U := Ub∩L ⁻¹' Us
  have hU : IsOpen U := hUb.inter (hUs.preimage L.continuous)
  let f := fun (φ : CoeffPair 2) (n : ℤ) => (Weight.sobolev (-b) n : ℂ)*
    Coeff.positiveWeightedCubicSums (Coeff.pairedOffDiagonalRow (fun n k => A.moment n k 2 (L φ))) n
  have hlocal (φ : CoeffPair 2) (hφ : φ∈U) :
      ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ∈T ∧ T⊆U ∧
        ∃ K : ℝ, 0≤K ∧ ∀ ψ∈T, ∃ c : Coeff 1, (∀ n, c n=f ψ n) ∧ ‖c‖≤K := by
    obtain ⟨T,hT,hφT,_hTU,K,hK,hb⟩ := hbounds φ hφ.1
    exact ⟨T∩U,hT.inter hU,⟨hφT,hφ⟩,(fun _ h => h.2),K,hK,fun ψ hψ => hb ψ hψ.1⟩
  have hformula (φ : CoeffPair 2) (hφ : φ∈U) (n : ℤ) :
      f φ n=(Weight.sobolev (-b) n : ℂ)*(if 0<n then
        A.weightedSecondMomentSum n (L φ)-(n : ℂ)*(A.moment n n 2 (L φ)-A.moment n (-n) 2 (L φ)) else 0) := by
    have he := A.pairedOffDiagonalSecondMomentSum_eq (L φ) n (hsum (L φ) hφ.2 n)
    dsimp only [f,Coeff.positiveWeightedCubicSums]
    by_cases hn : 0<n
    · rw [if_pos hn,if_pos hn,he]
    · rw [if_neg hn,if_neg hn]
  have hcoord (n : ℤ) : AnalyticOnNhd ℂ (fun φ => f φ n) U := by
    by_cases hn : 0<n
    · intro φ hφ
      have hm : AnalyticAt ℂ (fun χ => A.moment n n 2 (L χ)-A.moment n (-n) 2 (L χ)) φ :=
        ((A.analytic_moment n n 2 (L φ) (hUbV hφ.1).1).comp (L.analyticAt φ)).sub
          ((A.analytic_moment n (-n) 2 (L φ) (hUbV hφ.1).1).comp (L.analyticAt φ))
      have H : AnalyticAt ℂ (fun χ => (Weight.sobolev (-b) n : ℂ)*
          (A.weightedSecondMomentSum n (L χ)-(n : ℂ)*(A.moment n n 2 (L χ)-A.moment n (-n) 2 (L χ)))) φ :=
        analyticAt_const.mul (((ha n (L φ) hφ.2).comp (L.analyticAt φ)).sub (analyticAt_const.mul hm))
      apply H.congr
      filter_upwards [hU.mem_nhds hφ] with χ hχ
      rw [hformula χ hχ n,if_pos hn]
    · simpa only [f,Coeff.positiveWeightedCubicSums,if_neg hn,mul_zero] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : CoeffPair 2 => (0 : ℂ)) U)
  obtain ⟨hval,hpacket⟩ := Coeff.analytic_realization_of_local_bounds (r := 1) f hU hcoord (by
    intro φ hφ
    obtain ⟨T,hT,hφT,hTU,K,_hK,hb⟩ := hlocal φ hφ
    exact ⟨T,hT,hφT,hTU,K,hb⟩)
  refine ⟨U,hU,?_,(fun _ hφ => hUbV hφ.1),hpacket,(fun φ hφ n => (hval φ hφ n).trans (hformula φ hφ n)),?_⟩
  · intro φ hφ
    have hrφ := normalizedWeightedSource_realType w φ hφ
    exact ⟨hrealUb hφ,hrealUs hrφ⟩
  · intro φ hφ
    obtain ⟨T,hT,hφT,hTU,K,hK,hb⟩ := hlocal φ hφ
    refine ⟨T,hT,hφT,hTU,K,hK,?_⟩
    intro ψ hψ
    obtain ⟨b,hb,hbn⟩ := hb ψ hψ
    change ‖Coeff.ofFunctionOrZero 1 (f ψ)‖≤K
    rwa [Coeff.ofFunctionOrZero_eq_of_coordinates _ b hb]

end NLS.ZakharovShabat
