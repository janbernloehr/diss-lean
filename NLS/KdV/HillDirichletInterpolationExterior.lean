import NLS.KdV.HillWeightedDirichletExterior
import NLS.KdV.HillExteriorNumeratorVariationBound
import NLS.KdV.HillGapRootHilbertCoordinates
import NLS.KdV.HillGlobalNormalizedDifferentials
import NLS.KdV.HillFreeAbelianQuotient

/-! # Actual exterior decay for Hill Dirichlet interpolation -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
  rw [map_zero]
  exact Submodule.zero_mem _

private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
  rw [map_zero]
  intro k
  simp

/-- The exact free entire numerator identity, with no cut or zero-energy
exception, follows from the verified canonical product normalization. -/
theorem hillFreeAbelianPsi_frequency_identity (n : ℕ) (hn : 1≤n) (z : ℂ) :
    z*((freeHillValue n : ℂ)-z^2)*hillAbelianPsiCandidate hillFreeGapRoot n (z^2)=
      2*((n : ℂ)*Real.pi)*sin z := by
  let E := z^2
  let c : ℂ := (n : ℂ)*Real.pi
  have hc : c≠0 := mul_ne_zero (by exact_mod_cast (by omega : n≠0)) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hEn : (freeHillValue n : ℂ)=c^2 := by
    simp only [freeHillValue,Int.cast_natCast,c]
    push_cast
    ring
  have hroot : hillEnergyCanonicalRootProduct 0 zero_parity zero_real E=
      (-2*I)*Complex.sqrt E*(((freeHillValue n : ℂ)-E)/(freeHillValue n : ℂ)*hillAbelianNumeratorProduct hillFreeGapRoot n E) := by
    rw [hillEnergyCanonicalRootProduct,hillRealLabels_zero_ground zero_parity zero_real,
      ofReal_zero,sub_zero,hillFreeEnergyRootProduct_factorization zero_parity zero_real n hn E,
      hillEnergyRootFactor_zero zero_parity zero_real n hn]
    congr 2
    rw [sub_div,div_self (hEn ▸ pow_ne_zero 2 hc)]
  rw [hillEnergyCanonicalRootProduct_zero zero_parity zero_real E] at hroot
  have hsin : sin (Complex.sqrt E)=Complex.sqrt E*
      (((freeHillValue n : ℂ)-E)/(freeHillValue n : ℂ)*hillAbelianNumeratorProduct hillFreeGapRoot n E) := by
    apply mul_left_cancel₀ (show (-2*I : ℂ)≠0 by norm_num)
    exact hroot.trans (by ring)
  have hnum : Complex.sqrt E*((freeHillValue n : ℂ)-E)*hillAbelianPsiCandidate hillFreeGapRoot n E=
      2*c*sin (Complex.sqrt E) := by
    rw [hsin,hillAbelianPsiCandidate,hEn]
    change Complex.sqrt E*(c^2-E)*(2/c*hillAbelianNumeratorProduct hillFreeGapRoot n E)=_
    field_simp
  have hs : (Complex.sqrt E)^2=z^2 := complex_sqrt_sq E
  rcases eq_or_eq_neg_of_sq_eq_sq (Complex.sqrt E) z hs with h | h
  · simpa only [h,E,c] using hnum
  · rw [h,Complex.sin_neg] at hnum
    change z*((freeHillValue n : ℂ)-z^2)*hillAbelianPsiCandidate hillFreeGapRoot n (z^2)=_
    linear_combination -hnum

/-- Uniform actual quotient decay for every complex Hilbert numerator
and every bounded complex L2 potential family on the separated exterior. -/
theorem exists_hillAbelianHilbertPsi_dirichlet_exterior_bound (n : ℕ) (hn : 1≤n) (B : ℝ) :
    ∃ R C : ℝ, 0<R ∧ 0<C ∧ ∀ q : Coeff 2, ‖q‖≤B → ∀ a : Coeff 2, ∀ z : ℂ,
      R≤‖z‖ → (∀ m : ℤ, Real.pi/4≤‖z-(Real.pi : ℂ)*m‖) →
      hillL2DirichletCharacteristic q (z^2)≠0 ∧
        ‖hillAbelianHilbertPsi n (z^2,a)/hillL2DirichletCharacteristic q (z^2)‖≤
          C*Real.exp (‖a‖*hillExteriorWeightBound)/‖z‖^2 := by
  obtain ⟨C,hC,hcut⟩ := exists_hillL2Dirichlet_exterior_lower_bound (by positivity : 0<Real.pi/4)
  obtain ⟨R,hR,hD⟩ := hcut B
  have hnR : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  refine ⟨max R (max 1 (2*‖(freeHillValue n : ℂ)‖)),4*((n : ℝ)*Real.pi)*C,
    lt_of_lt_of_le hR (le_max_left _ _),by positivity,?_⟩
  intro q hq a z hz hsep
  have hzR : R≤‖z‖ := (le_max_left _ _).trans hz
  have hz0 : 0<‖z‖ := hR.trans_le hzR
  have hz1 : 1≤‖z‖ := (le_max_left _ _).trans ((le_max_right _ _).trans hz)
  have hzE : 2*‖(freeHillValue n : ℂ)‖≤‖z‖ := (le_max_right _ _).trans ((le_max_right _ _).trans hz)
  obtain ⟨hDn,hDb⟩ := hD q hq z hzR hsep
  refine ⟨hDn,?_⟩
  have hgap : ‖z‖^2/2≤‖(freeHillValue n : ℂ)-z^2‖ := by
    have ht := norm_sub_norm_le (z^2) (freeHillValue n : ℂ)
    rw [norm_pow,norm_sub_rev] at ht
    nlinarith [mul_nonneg (sub_nonneg.mpr hz1) (norm_nonneg z)]
  have hf : ‖z‖*‖(freeHillValue n : ℂ)-z^2‖*‖hillAbelianPsiCandidate hillFreeGapRoot n (z^2)‖=
      2*((n : ℝ)*Real.pi)*‖sin z‖ := by
    simpa only [norm_mul,norm_ofNat,norm_natCast,norm_real,Real.norm_of_nonneg Real.pi_pos.le] using
      congrArg norm (hillFreeAbelianPsi_frequency_identity n hn z)
  have hfree : ‖(freeHillValue n : ℂ)-z^2‖*‖hillAbelianPsiCandidate hillFreeGapRoot n (z^2)‖≤
      2*((n : ℝ)*Real.pi)*C*‖hillL2DirichletCharacteristic q (z^2)‖ := by
    apply (mul_le_mul_iff_left₀ hz0).mp
    calc
      _ = 2*((n : ℝ)*Real.pi)*‖sin z‖ := by linear_combination hf
      _ ≤ 2*((n : ℝ)*Real.pi)*Real.exp |z.im| :=
        mul_le_mul_of_nonneg_left (norm_complex_sin_le_exp_im z) (by positivity)
      _ ≤ 2*((n : ℝ)*Real.pi)*(C*‖z‖*‖hillL2DirichletCharacteristic q (z^2)‖) :=
        mul_le_mul_of_nonneg_left hDb (by positivity)
      _ = _ := by ring
  have hp := norm_hillAbelianHilbertPsi_exterior_le n z
    (notMem_freeLattice_of_separated (by positivity : 0<Real.pi/4) hsep) hsep a
  rw [norm_div]
  apply (div_le_div_iff₀ (norm_pos_iff.mpr hDn) (sq_pos_of_pos hz0)).mpr
  calc
    _ ≤ (‖hillAbelianPsiCandidate hillFreeGapRoot n (z^2)‖*Real.exp (‖a‖*hillExteriorWeightBound))*‖z‖^2 :=
      mul_le_mul_of_nonneg_right hp (sq_nonneg ‖z‖)
    _ = 2*Real.exp (‖a‖*hillExteriorWeightBound)*
        ((‖z‖^2/2)*‖hillAbelianPsiCandidate hillFreeGapRoot n (z^2)‖) := by ring
    _ ≤ 2*Real.exp (‖a‖*hillExteriorWeightBound)*
        (‖(freeHillValue n : ℂ)-z^2‖*‖hillAbelianPsiCandidate hillFreeGapRoot n (z^2)‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgap (norm_nonneg _)) (by positivity)
    _ ≤ 2*Real.exp (‖a‖*hillExteriorWeightBound)*
        (2*((n : ℝ)*Real.pi)*C*‖hillL2DirichletCharacteristic q (z^2)‖) :=
      mul_le_mul_of_nonneg_left hfree (by positivity)
    _ = _ := by ring

/-- The actual canonically normalized numerator divided by the actual
Dirichlet characteristic decays on the full separated exterior. No
Dirichlet product formula or interpolation identity is assumed. -/
theorem exists_hillAbelianSelectedGlobalPsi_dirichlet_exterior_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) :
    ∃ R C : ℝ, 0<R ∧ 0<C ∧ ∀ z : ℂ, R≤‖z‖ →
      (∀ m : ℤ, Real.pi/4≤‖z-(Real.pi : ℂ)*m‖) →
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) (z^2)≠0 ∧
        ‖hillAbelianSelectedGlobalPsi q hq hr n hn (z^2)/
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) (z^2)‖≤C/‖z‖^2 := by
  let σ := (hillAbelianSelectedGlobalRoots q hq hr n hn).val
  have hσ : σ∈hillGapRootBox q hq hr := (hillAbelianSelectedGlobalRoots q hq hr n hn).property
  let a := hillGapRootHilbertCoordinates q hq hr σ hσ
  let N := hillAbelianCandidatePeriod q hq hr σ n n
  have hN : N≠0 := hillAbelianCandidatePeriod_own_ne_zero q hq hr σ hσ n hn
  obtain ⟨R,C,hR,hC,hbound⟩ := exists_hillAbelianHilbertPsi_dirichlet_exterior_bound n hn ‖SpectralWeight.one.toCoeff q‖
  refine ⟨R,C*Real.exp (‖a‖*hillExteriorWeightBound)/‖N‖,hR,by positivity,?_⟩
  intro z hz hsep
  obtain ⟨hD,hb⟩ := hbound (SpectralWeight.one.toCoeff q) le_rfl a z hz hsep
  refine ⟨hD,?_⟩
  have he : hillAbelianSelectedGlobalPsi q hq hr n hn (z^2)/hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) (z^2)=
      (hillAbelianHilbertPsi n (z^2,a)/hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) (z^2))/N := by
    rw [hillAbelianHilbertPsi_eq_genuine_candidate q hq hr σ hσ n (z^2)]
    change (hillAbelianPsiCandidate σ n (z^2)/N)/_= _
    ring
  rw [he,norm_div]
  apply (div_le_div_of_nonneg_right hb (norm_nonneg N)).trans_eq
  ring

/-- Actual energy-circle quotient decay, on the same expanding circles
used for the source interpolation and with zero-free denominator. -/
theorem eventually_hillAbelianSelectedGlobalPsi_dirichlet_circle_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) :
    ∃ K : ℕ, ∃ C : ℝ, 0<C ∧ ∀ k : ℕ, K≤k → ∀ E∈sphere (0 : ℂ) ((centralCircleRadius k)^2),
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E≠0 ∧
      ‖hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E‖≤
        C/(centralCircleRadius k)^2 := by
  obtain ⟨R,C,_hR,hC,hbound⟩ := exists_hillAbelianSelectedGlobalPsi_dirichlet_exterior_bound q hq hr n hn
  obtain ⟨K,hK⟩ := exists_nat_gt (R/Real.pi)
  refine ⟨K,C,hC,?_⟩
  intro k hk E hE
  have hrad := centralCircleRadius_pos k
  have hnorm : ‖E‖=(centralCircleRadius k)^2 := by simpa only [mem_sphere,dist_zero_right] using hE
  have hs : ‖Complex.sqrt E‖=centralCircleRadius k := by
    have ht := congrArg norm (complex_sqrt_sq E)
    rw [norm_pow,hnorm] at ht
    nlinarith [norm_nonneg (Complex.sqrt E)]
  have hRk : R≤centralCircleRadius k := by
    have h1 : R<(K : ℝ)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp hK
    have h2 : (K : ℝ)≤k := by exact_mod_cast hk
    unfold centralCircleRadius
    nlinarith [Real.pi_pos]
  have hsep (m : ℤ) : Real.pi/4≤‖Complex.sqrt E-(Real.pi : ℂ)*m‖ := by
    have hh := centralCircle_lattice_gap k (show Complex.sqrt E∈sphere (0 : ℂ) (centralCircleRadius k) by
      simpa only [mem_sphere,dist_zero_right] using hs) m
    linarith [Real.pi_pos]
  simpa only [complex_sqrt_sq,hs] using hbound (Complex.sqrt E) (by rw [hs];exact hRk) hsep

/-- The actual outer Cauchy error tends to zero uniformly for bounded
energy evaluations. The infinite interpolation identity is not assumed. -/
theorem eventually_hillDirichlet_outerCauchy_small
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n)
    (L : ℝ) (hL : 0≤L) {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℕ, ∀ k : ℕ, K≤k → ∀ w : ℂ, ‖w‖≤L →
      ‖∮ E in C(0,(centralCircleRadius k)^2),
        hillAbelianSelectedGlobalPsi q hq hr n hn E/
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E/(E-w)‖<ε := by
  obtain ⟨K₀,C,hC,hbound⟩ := eventually_hillAbelianSelectedGlobalPsi_dirichlet_circle_bound q hq hr n hn
  obtain ⟨K₁,hK₁⟩ := exists_nat_gt ((2*L+4*Real.pi*C/ε+1)/Real.pi)
  refine ⟨max K₀ K₁,?_⟩
  intro k hk w hw
  let R := (centralCircleRadius k)^2
  have hrad := centralCircleRadius_pos k
  have hR : 0<R := sq_pos_of_pos hrad
  have hlarge : 2*L+4*Real.pi*C/ε+1<R := by
    have h1 : 2*L+4*Real.pi*C/ε+1<(K₁ : ℝ)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp hK₁
    have h2 : (K₁ : ℝ)≤k := by exact_mod_cast ((le_max_right K₀ K₁).trans hk)
    have he : 0<4*Real.pi*C/ε := by positivity
    have hc : 2*L+4*Real.pi*C/ε+1<centralCircleRadius k := by
      unfold centralCircleRadius
      nlinarith [Real.pi_pos]
    dsimp only [R]
    nlinarith
  have h2L : 2*L<R := by
    have he : 0<4*Real.pi*C/ε := by positivity
    linarith
  have hpoint (E : ℂ) (hE : E∈sphere (0 : ℂ) R) :
      ‖hillAbelianSelectedGlobalPsi q hq hr n hn E/
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E/(E-w)‖≤2*C/R^2 := by
    have hb := (hbound k ((le_max_left _ _).trans hk) E hE).2
    change ‖hillAbelianSelectedGlobalPsi q hq hr n hn E/
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E‖≤C/R at hb
    have hnorm : ‖E‖=R := by simpa only [mem_sphere,dist_zero_right] using hE
    have ht := norm_add_le (E-w) w
    rw [sub_add_cancel,hnorm] at ht
    have hdist : R/2≤‖E-w‖ := by linarith
    rw [norm_div]
    calc
      _ ≤ (C/R)/(R/2) := (div_le_div_of_nonneg_right hb (norm_nonneg _)).trans
        (div_le_div_of_nonneg_left (by positivity : 0≤C/R) (half_pos hR) hdist)
      _ = _ := by field_simp
  have hi := circleIntegral.norm_integral_le_of_norm_le_const hR.le hpoint
  have heq : 2*Real.pi*R*(2*C/R^2)=4*Real.pi*C/R := by field_simp; ring
  rw [heq] at hi
  apply hi.trans_lt
  apply (div_lt_iff₀ hR).mpr
  have hs : 4*Real.pi*C/ε<R := by linarith
  have ht := (div_lt_iff₀ hε).mp hs
  nlinarith

end NLS.KdV
