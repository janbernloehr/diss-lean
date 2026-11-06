import NLS.KdV.HillHighDeflatedDiscBounds
import NLS.KdV.HillLocalNormalizedHilbertParameters

/-! # Locally uniform inverse-square tails for the original normalized differential -/
noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem exists_local_hillAbelianCosineDifferential_sq_decay
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ L : ℝ, 0 < L ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q, ∀ k : ℕ, N ≤ k → ∀ θ : ℝ,
        ‖hillAbelianCosineDifferential p.val p.property.1 p.property.2 n hn k (θ : ℂ)‖ ≤
          L/(k : ℝ)^2 := by
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈
      Coeff.paritySubspace 0 := by rw [map_zero];exact (Coeff.paritySubspace 0).zero_mem
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    rw [map_zero]
    intro j
    simp
  obtain ⟨a,c,ha,hc,hc0,hmatch⟩ :=
    exists_hillAbelianSelectedGlobalPsi_local_Hilbert_parameters q.val q.property.1 q.property.2 h0q h0r n hn
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  let B := ‖P q‖+1
  let A := ‖a (P q)‖+1
  let d := ‖c (P q)‖/2
  have hd : 0 < d := by exact half_pos (norm_pos_iff.mpr hc0)
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have haP : ContinuousAt (fun p => a (P p)) q := ha.continuousAt.comp (f := P) (x := q) hP.continuousAt
  have hcP : ContinuousAt (fun p => c (P p)) q := hc.continuousAt.comp (f := P) (x := q) hP.continuousAt
  have hnearB : ∀ᶠ p in 𝓝 q, ‖P p‖ ≤ B :=
    (hP.continuousAt.norm.eventually (Iio_mem_nhds (lt_add_one ‖P q‖))).mono (fun _ h => h.le)
  have hnearA : ∀ᶠ p in 𝓝 q, ‖a (P p)‖ ≤ A :=
    (haP.norm.eventually (Iio_mem_nhds (lt_add_one ‖a (P q)‖))).mono (fun _ h => h.le)
  have hneard : ∀ᶠ p in 𝓝 q, d ≤ ‖c (P p)‖ :=
    (hcP.norm.eventually (Ioi_mem_nhds (by dsimp only [d];linarith [norm_pos_iff.mpr hc0]))).mono
      (fun _ h => h.le)
  obtain ⟨N,hN,K,hK,hbound⟩ := exists_hillHighGap_deflatedHilbertPsi_sq_decay h0q h0r B hB n hn
  let L := K*(n : ℝ)*Real.exp ((8/Real.pi^2)*A)/d
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨N,hN,L,by dsimp only [L];positivity,?_⟩
  filter_upwards [hnearB,hnearA,hneard,hmatch] with p hpB hpA hpd hpm
  intro k hk θ
  let E := cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
    (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (θ : ℂ)
  have hb := hbound p hpB (a (P p)) k hk θ
  have he : Real.exp ((8/Real.pi^2)*‖a (P p)‖) ≤ Real.exp ((8/Real.pi^2)*A) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpA (by positivity))
  have hb' : ‖hillAbelianHilbertPsi n (E,a (P p))/
      hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k E‖ ≤
      K*(n : ℝ)*Real.exp ((8/Real.pi^2)*A)/(k : ℝ)^2 :=
    hb.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (sq_nonneg _))
  change ‖-I*(hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn E/
    hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k E)‖ ≤ _
  rw [← hpm E,div_right_comm,norm_mul,norm_neg,norm_I,one_mul,norm_div]
  apply (div_le_div_of_nonneg_right hb' (norm_nonneg _)).trans
  apply (div_le_div_of_nonneg_left (by positivity) hd hpd).trans_eq
  dsimp only [L]
  ring

end NLS.KdV
