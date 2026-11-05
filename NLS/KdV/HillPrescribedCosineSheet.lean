import NLS.KdV.HillGlobalRegularCorrection
import NLS.KdV.HillRealGapSigns
import NLS.KdV.HillDeflatedRadicandFactorization
import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot

/-! The ORIGINAL physical terminal fixes the sign of the prescribed
energy root along each connected regular real cosine arc. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
  (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
  (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillCosine_regular_mem_open_gap (k : ℕ) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q hq hr k≠0) (θ : ℝ) (hs : Real.sin θ≠0) :
    (cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) (θ:ℂ)).re∈
      Ioo (hillRealLabels q hq hr (2*k-1)) (hillRealLabels q hq hr (2*k)) := by
  have hm := monotone_hillRealLabels q hq hr (by omega : 2*k-1≤2*k)
  have hδ : 0<hillRealGapHalfLength q hq hr k := by
    have hn : 0≤hillRealGapHalfLength q hq hr k := by
      unfold hillRealGapHalfLength
      linarith
    exact lt_of_le_of_ne hn (Ne.symm hgap)
  have hc : -1<Real.cos θ ∧ Real.cos θ<1 := by
    have he := Real.sin_sq_add_cos_sq θ
    have hn := sq_pos_of_ne_zero hs
    constructor <;> nlinarith
  have hl := mul_lt_mul_of_pos_left hc.1 hδ
  have hu := mul_lt_mul_of_pos_left hc.2 hδ
  have hg := hillRealGapContour_geometry q hq hr k hk
  simp only [cosineGapPoint,← Complex.ofReal_cos,← ofReal_mul,← ofReal_add,ofReal_re]
  rw [← hg.2.2.1,← hg.2.2.2.1]
  constructor <;> linarith

theorem hillPrescribedRoot_real_gap_domain (k : ℕ) (hk : 1≤k)
    (w : ℂ) (hw : w≠0) (hwr : w.im=0) (x : ℝ)
    (hx : x∈Ioo (hillRealLabels q hq hr (2*k-1)) (hillRealLabels q hq hr (2*k))) :
    (x:ℂ)∈prescribedSquareRootDomain (hillL2Radicand (SpectralWeight.one.toCoeff q)) w := by
  have hrpos := hillL2Radicand_pos_gap q hq hr k hk x hx
  have hR : hillL2Radicand (SpectralWeight.one.toCoeff q) (x:ℂ)=
      ((hillL2Radicand (SpectralWeight.one.toCoeff q) (x:ℂ)).re:ℂ) :=
    Complex.ext rfl (by simpa only [ofReal_im] using hillL2Radicand_real _ hr x)
  have hwe : w=(w.re:ℂ) := Complex.ext rfl (by simpa only [ofReal_im] using hwr)
  have hwn : w.re≠0 := by intro he; apply hw; rw [hwe,he,ofReal_zero]
  change hillL2Radicand (SpectralWeight.one.toCoeff q) (x:ℂ)/w^2∈slitPlane
  rw [hR,hwe,← ofReal_pow,← ofReal_div]
  exact Complex.mem_slitPlane_iff.mpr (Or.inl (by
    simpa only [ofReal_re] using div_pos hrpos (sq_pos_of_ne_zero hwn)))

theorem hillPrescribedRoot_cosine_domain (k : ℕ) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q hq hr k≠0)
    (w : ℂ) (hw : w≠0) (hwr : w.im=0) (θ : ℝ) (hs : Complex.sin (θ:ℂ)≠0) :
    cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) (θ:ℂ)∈
      prescribedSquareRootDomain (hillL2Radicand (SpectralWeight.one.toCoeff q)) w := by
  have hsr : Real.sin θ≠0 := by
    intro h
    apply hs
    rw [← Complex.ofReal_sin,h,ofReal_zero]
  have he : cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) (θ:ℂ)=
      (((cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) (θ:ℂ)).re):ℂ) := by
    simp only [cosineGapPoint,← ofReal_cos,← ofReal_mul,← ofReal_add,ofReal_re]
  rw [he]
  exact hillPrescribedRoot_real_gap_domain q hq hr k hk w hw hwr _
    (hillCosine_regular_mem_open_gap q hq hr k hk hgap θ hsr)

/-- The prescribed root along a connected regular real cosine arc is
EXACTLY the root determined by the ORIGINAL physical terminal sine.
The sign is fixed by its actual value, rather than by squared identities. -/
theorem hillPrescribedDirichletRoot_cosine_eq (k : ℕ) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q hq hr k≠0)
    (S : Set ℂ) (hS : IsPreconnected S) (hreal : ∀ θ∈S, θ.im=0)
    (hSin : ∀ θ∈S, Complex.sin θ≠0) (e : ℂ) (he : e∈S)
    (hpoint : cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) e=
      (hillDirichletEnergy q hq hr k hk:ℂ))
    (hsin : Complex.sin e=hillDirichletGapSine q hq hr k hk)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q)
      (hillDirichletEnergy q hq hr k hk)≠0) :
    ∀ θ∈S, prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q))
      (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr k hk))
        (cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) θ)=
      -I*(hillRealGapHalfLength q hq hr k:ℂ)*Complex.sin θ*
        hillDeflatedEnergyCanonicalRoot q hq hr k
          (cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) θ) := by
  let τ : ℂ := hillRealGapCenter q hq hr k
  let δ : ℂ := hillRealGapHalfLength q hq hr k
  let T := cosineGapPoint τ δ
  let D := hillDeflatedEnergyCanonicalRoot q hq hr k
  let f := hillL2Radicand (SpectralWeight.one.toCoeff q)
  let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr k hk)
  let R := prescribedSquareRoot f w
  let G : ℂ → ℂ := fun θ => -I*δ*Complex.sin θ*D (T θ)
  have hδ : δ≠0 := ofReal_ne_zero.mpr hgap
  have hθ (θ : ℂ) (hθ : θ∈S) : θ=(θ.re:ℂ) := Complex.ext rfl (by simpa using hreal θ hθ)
  have hfill (θ : ℂ) (hθS : θ∈S) : T θ∈hillGapFilledDomain q hq hr k := by
    rw [hθ θ hθS]
    exact hillCosineGapPoint_mem_filledDomain q hq hr k hk θ.re
  have hDne (θ : ℂ) (hθS : θ∈S) : D (T θ)≠0 :=
    hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk _ (hfill θ hθS)
  have hwr : w.im=0 := by
    dsimp only [w]
    rw [hillDirichletSheetRoot_at_dirichlet_eq_norming q hq hr k hk]
    exact ofReal_im _
  have hdom (θ : ℂ) (hθS : θ∈S) : T θ∈prescribedSquareRootDomain f w := by
    rw [hθ θ hθS]
    exact hillPrescribedRoot_cosine_domain q hq hr k hk hgap w hw hwr θ.re
      (by rw [← hθ θ hθS];exact hSin θ hθS)
  have hT : Continuous T := by
    change Continuous (fun θ : ℂ => τ+δ*Complex.cos θ)
    fun_prop
  have hRc : ContinuousOn (fun θ => R (T θ)) S := by
    intro θ hθS
    exact (((analyticOnNhd_prescribedSquareRoot f w (analyticOnNhd_hillL2Radicand _))
      _ (hdom θ hθS)).continuousAt.comp hT.continuousAt).continuousWithinAt
  have hDc : ContinuousOn (fun θ => D (T θ)) S := by
    intro θ hθS
    exact ((analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k _
      (hfill θ hθS)).continuousAt.comp hT.continuousAt).continuousWithinAt
  have hGc : ContinuousOn G S := ((continuousOn_const.mul continuousOn_const).mul
    Complex.continuous_sin.continuousOn).mul hDc
  have hGne (θ : ℂ) (hθS : θ∈S) : G θ≠0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hδ)
      (hSin θ hθS)) (hDne θ hθS)
  have hsq (θ : ℂ) (hθS : θ∈S) : (R (T θ))^2=(G θ)^2 := by
    rw [show R (T θ)^2=f (T θ) from prescribedSquareRoot_sq f w hw _]
    have hf := hillL2Radicand_eq_gap_polynomial_mul_deflated_sq q hq hr k hk (T θ) (hfill θ hθS)
    have hg := hillRealGapContour_geometry q hq hr k hk
    have hl : (hillRealLabels q hq hr (2*k-1):ℂ)=τ-δ := by
      dsimp only [τ,δ]
      rw [← ofReal_sub,hg.2.2.1]
    have hu : (hillRealLabels q hq hr (2*k):ℂ)=τ+δ := by
      dsimp only [τ,δ]
      rw [← ofReal_add,hg.2.2.2.1]
    rw [hl,hu] at hf
    have hp : (T θ-(τ-δ))*(T θ-(τ+δ))= -(δ^2*Complex.sin θ^2) := by
      calc
        _ = (τ-δ-T θ)*(τ+δ-T θ) := by ring
        _ = _ := cosineGapPoint_endpoint_factor τ δ θ
    rw [hp] at hf
    change f (T θ)=_ at hf
    rw [hf]
    dsimp only [G,D]
    ring_nf
    simp
  have hbase : R (T e)=G e := by
    have hs := hillDirichletSheetRoot_sq_of_characteristic_zero
      (SpectralWeight.one.toCoeff q) _ (hillDirichletEnergy_zero q hq hr k hk)
    have hRbase : R (T e)=w := by
      rw [show T e=(hillDirichletEnergy q hq hr k hk:ℂ) from hpoint]
      exact prescribedSquareRoot_base f w hw _ hs.symm
    rw [hRbase]
    dsimp only [G]
    rw [show T e=(hillDirichletEnergy q hq hr k hk:ℂ) from hpoint,hsin,hillDirichletGapSine]
    have hd := hDne e he
    rw [show T e=(hillDirichletEnergy q hq hr k hk:ℂ) from hpoint] at hd
    dsimp only [w,D,δ] at *
    field_simp [hgap,hd]
    simp
  exact hS.eq_of_sq_eq hRc hGc hsq (fun {θ} hθS => hGne θ hθS) he hbase


/-- The ORIGINAL cosine differential is the exact pullback of the
terminal-prescribed ORIGINAL energy differential on the same arc. -/
theorem hillPrescribedDirichletDifferential_cosine_pullback (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q hq hr k≠0)
    (S : Set ℂ) (hS : IsPreconnected S) (hreal : ∀ θ∈S, θ.im=0)
    (hSin : ∀ θ∈S, Complex.sin θ≠0) (e : ℂ) (he : e∈S)
    (hpoint : cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) e=
      (hillDirichletEnergy q hq hr k hk:ℂ))
    (hsin : Complex.sin e=hillDirichletGapSine q hq hr k hk)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q)
      (hillDirichletEnergy q hq hr k hk)≠0) :
    ∀ θ∈S, (hillAbelianSelectedGlobalPsi q hq hr n hn
        (cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) θ)/
      prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q))
        (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr k hk))
          (cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) θ))*
      (-(hillRealGapHalfLength q hq hr k:ℂ)*Complex.sin θ)=
        hillAbelianCosineDifferential q hq hr n hn k θ := by
  intro θ hθ
  rw [hillPrescribedDirichletRoot_cosine_eq q hq hr k hk hgap S hS hreal hSin e he hpoint hsin hw θ hθ,
    hillAbelianCosineDifferential]
  have hθreal : θ=(θ.re:ℂ) := Complex.ext rfl (by simpa using hreal θ hθ)
  have hfill := hillCosineGapPoint_mem_filledDomain q hq hr k hk θ.re
  rw [← hθreal] at hfill
  have hD := hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk _ hfill
  field_simp [ofReal_ne_zero.mpr hgap,hSin θ hθ,hD]
  ring_nf
  simp

end NLS.KdV
