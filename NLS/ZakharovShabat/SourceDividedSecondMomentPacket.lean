import NLS.ZakharovShabat.SourceWeightedSecondMomentSums
import NLS.SequenceSpaces.DividedCubicFrequencyPacket

/-! The actual signed index-weighted second moments, divided by the own
positive index, form a genuine Banach-analytic ellr packet for EVERY r>1
near ALL real Hilbert sources. Refined cubic rows retain the reciprocal
convolution decay and the SAME actual squared-gap/numerator branch. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable {r : ℝ≥0∞} [Fact (1 ≤ r)]

def SourceAbelianMomentAtlas.positiveDividedSecondMomentPacket
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (r : ℝ≥0∞) (ψ : CoeffPair 2) : Coeff r :=
  Coeff.ofFunctionOrZero r (Coeff.positiveDividedCubicSums (fun n k => A.moment n k 2 ψ))

theorem SourceAbelianMomentAtlas.exists_analytic_dividedSecondMomentPacket
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2⊆V) (hr : 1<r) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ realTypeSourceLocus 2⊆U ∧ U⊆A.domain∩V ∧
      AnalyticOnNhd ℂ (A.positiveDividedSecondMomentPacket r) U ∧
      (∀ ψ∈U, ∀ n : ℤ, A.positiveDividedSecondMomentPacket r ψ n=
        if 0<n then A.weightedSecondMomentSum n ψ/(n : ℂ) else 0) ∧
      ∀ φ∈U, ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ∈T ∧ T⊆U ∧
        ∃ K : ℝ, 0≤K ∧ ∀ ψ∈T, ‖A.positiveDividedSecondMomentPacket r ψ‖≤K := by
  obtain ⟨Us,hUs,_hUsc,hrealUs,hUsV,hsum,ha,_hconv,_hlocalUs⟩ :=
    A.exists_analytic_weightedSecondMomentSum hs hV hrealV
  obtain ⟨Ur,hUr,_hUrc,hrealUr,hUrV,hrows⟩ := A.exists_lemma20_3_refined hs hV hrealV
  let U := Us∩Ur
  have hU : IsOpen U := hUs.inter hUr
  let f := fun (ψ : CoeffPair 2) => Coeff.positiveDividedCubicSums (fun n k => A.moment n k 2 ψ)
  have hlocal (φ : CoeffPair 2) (hφ : φ∈U) :
      ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ∈T ∧ T⊆U ∧
        ∃ K : ℝ, 0≤K ∧ ∀ ψ∈T, ∃ b : Coeff r, (∀ n, b n=f ψ n) ∧ ‖b‖≤K := by
    obtain ⟨ρ,hρ,hball,hcoeff⟩ := hrows φ hφ.2
    obtain ⟨M,hM,hdata⟩ := hcoeff 2 (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨_,_,G,hG,hφG,R,hR,hgap⟩ :=
      exists_uniform_small_sourcePeriodicGapDisplacement (p := 2) (by norm_num) (by norm_num) φ
        (by norm_num : (0 : ℝ)<1)
    let T := (ball φ ρ∩G)∩Us
    let D := (Real.pi+M)/4
    let K := D*R^2+2*M*‖Coeff.puncturedLattice r hr‖*R^3
    have hD : 0≤D := by dsimp only [D];positivity
    have hK : 0≤K := by dsimp only [K];positivity
    refine ⟨T,(isOpen_ball.inter hG).inter hUs,⟨⟨mem_ball_self hρ,hφG⟩,hφ.1⟩,
      (fun ψ hψ => ⟨hψ.2,hball hψ.1.1⟩),K,hK,?_⟩
    intro ψ hψ
    obtain ⟨d,_hdval,hdnorm,hdfactor,hoff⟩ := hdata ψ hψ.1.1
    have hdiag (n : ℤ) : ‖A.moment n n 2 ψ‖≤D*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ n‖^2 := by
      rw [hdfactor n,norm_mul,norm_div,norm_pow]
      have hdn := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0) d n).trans hdnorm
      have hb : ‖(Real.pi : ℂ)+d n‖≤Real.pi+M := by
        apply (norm_add_le _ _).trans
        simpa only [Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le] using add_le_add le_rfl hdn
      norm_num only [Complex.norm_ofNat]
      calc
        _≤‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ n‖^2/4*(Real.pi+M) := by gcongr
        _=_ := by dsimp only [D];ring
    exact Coeff.exists_positive_divided_cubic_packet hr
      (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ)
      (fun n k => A.moment n k 2 ψ) R D M hR hD hM.le (hgap ψ hψ.1.2).1 hdiag
      (fun n => by obtain ⟨a,_haval,_han,hanorm,hafactor⟩ := hoff n;exact ⟨a,hanorm,hafactor⟩)
      (hsum ψ hψ.2)
  have hcoord (n : ℤ) : AnalyticOnNhd ℂ (fun ψ => f ψ n) U := by
    by_cases hn : 0<n
    · intro ψ hψ
      have hh : AnalyticAt ℂ (fun χ => A.weightedSecondMomentSum n χ/(n : ℂ)) ψ :=
        (ha n ψ hψ.1).div_const
      exact hh.congr (Eventually.of_forall (fun _ => (if_pos hn).symm))
    · simpa only [f,Coeff.positiveDividedCubicSums,if_neg hn] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : CoeffPair 2 => (0 : ℂ)) U)
  obtain ⟨hval,hpacket⟩ := Coeff.analytic_realization_of_local_bounds (r := r) f hU hcoord (by
    intro φ hφ
    obtain ⟨T,hT,hφT,hTU,K,_hK,hb⟩ := hlocal φ hφ
    exact ⟨T,hT,hφT,hTU,K,hb⟩)
  refine ⟨U,hU,(fun ψ hψ => ⟨hrealUs hψ,hrealUr hψ⟩),(fun ψ hψ => hUsV hψ.1),hpacket,
    (fun ψ hψ n => hval ψ hψ n),?_⟩
  intro φ hφ
  obtain ⟨T,hT,hφT,hTU,K,hK,hb⟩ := hlocal φ hφ
  refine ⟨T,hT,hφT,hTU,K,hK,?_⟩
  intro ψ hψ
  obtain ⟨b,hb,hbn⟩ := hb ψ hψ
  change ‖Coeff.ofFunctionOrZero r (f ψ)‖≤K
  rwa [Coeff.ofFunctionOrZero_eq_of_coordinates _ b hb]

end NLS.ZakharovShabat
