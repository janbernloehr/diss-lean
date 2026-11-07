import NLS.ZakharovShabat.SourceDividedSecondMomentPacket

/-! The actual refined second-moment rows have simultaneous scalar norm
bounds before all own and summation indices, on a common complex ball.
All factors come from the SAME checked numerator and squared-gap branch. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem SourceAbelianMomentAtlas.exists_local_refinedCubicNormBounds
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2⊆V) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ realTypeSourceLocus 2⊆U ∧ U⊆A.domain∩V ∧
      ∀ φ∈U, ∃ ρ : ℝ, 0<ρ ∧ ball φ ρ⊆U ∧
        ∃ D M : ℝ, 0≤D ∧ 0≤M ∧ ∀ ψ∈ball φ ρ,
          (∀ n : ℤ, ‖A.moment n n 2 ψ‖≤D*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ n‖^2) ∧
          ∀ n k : ℤ, k≠n → ‖A.moment n k 2 ψ‖≤M*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ k‖^3*
            ‖Coeff.puncturedLattice 2 (by norm_num) (n-k)‖ := by
  obtain ⟨U,hU,_hUc,hrealU,hUV,hrows⟩ := A.exists_lemma20_3_refined hs hV hrealV
  refine ⟨U,hU,hrealU,hUV,?_⟩
  intro φ hφ
  obtain ⟨ρ,hρ,hball,hcoeff⟩ := hrows φ hφ
  obtain ⟨M,hM,hdata⟩ := hcoeff 2 (by norm_num) (by norm_num) (by norm_num)
  let D := (Real.pi+M)/4
  have hD : 0≤D := by dsimp only [D];positivity
  refine ⟨ρ,hρ,hball,D,M,hD,hM.le,?_⟩
  intro ψ hψ
  obtain ⟨d,_hdval,hdnorm,hdfactor,hoff⟩ := hdata ψ hψ
  constructor
  · intro n
    rw [hdfactor n,norm_mul,norm_div,norm_pow]
    have hdn := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0) d n).trans hdnorm
    have hb : ‖(Real.pi : ℂ)+d n‖≤Real.pi+M := by
      apply (norm_add_le _ _).trans
      simpa only [Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le] using add_le_add le_rfl hdn
    norm_num only [Complex.norm_ofNat]
    calc
      _≤‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ n‖^2/4*(Real.pi+M) := by gcongr
      _=_ := by dsimp only [D];ring
  · intro n k hkn
    obtain ⟨b,_hbval,_hbn,hbnorm,hfactor⟩ := hoff n
    rw [hfactor k hkn,norm_mul,norm_div,norm_pow,Coeff.puncturedLattice_apply,
      if_neg (sub_ne_zero.mpr (Ne.symm hkn)),norm_inv]
    have hbk := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0) b k).trans hbnorm
    calc
      _≤‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ k‖^3/‖((n-k : ℤ) : ℂ)‖*M := by gcongr
      _=_ := by rw [div_eq_mul_inv];ring

end NLS.ZakharovShabat
