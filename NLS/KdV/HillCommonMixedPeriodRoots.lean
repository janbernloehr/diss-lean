import NLS.KdV.HillSelectedJointPeriodBounds
import NLS.ComplexAnalysis.QuantitativeNeumannAnalyticInverse
import NLS.ComplexAnalysis.QuantitativeTriangularDerivative
import NLS.ComplexAnalysis.BanachHolomorphicC1
import NLS.ComplexAnalysis.BanachAnalyticZeroBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Actual mixed-period roots around every original real source have
one complex source radius and one root radius, chosen before every
positive differential index, and local uniqueness on that root ball. -/
theorem exists_hillMixedSupportedPeriods_common_analytic_root :
    ∃ N : ℕ, ∃ B D ρ δ : ℝ, 1≤N ∧ 0<B ∧ 0<D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
      0<ρ ∧ 0<δ ∧ ball (SpectralWeight.one.toCoeff q) δ⊆ball 0 B ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ s : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ),
        AnalyticOnNhd ℂ s (ball (SpectralWeight.one.toCoeff q) δ) ∧ s (SpectralWeight.one.toCoeff q)=0 ∧
        ∀ p∈ball (SpectralWeight.one.toCoeff q) δ,
          (s p,p)∈ball (0,SpectralWeight.one.toCoeff q) ρ ∧
          hillMixedSupportedPeriodMap q hq hr h0q h0r N n (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn) (s p,p)=0 ∧
          ∀ h∈ball (0 : PositiveDeletedCoeff 2 (n : ℤ)) ρ,
            hillMixedSupportedPeriodMap q hq hr h0q h0r N n (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn) (h,p)=0 → h=s p := by
  obtain ⟨N,Bpot,Dpot,R,M,C,hN,hBpot,hDpot,hc,hR,hM,hC,hsource,hdata⟩ :=
    exists_hillSelectedMixedPeriodJointMap_common_bounds q hq hr h0q h0r
  let BJ := C*(1+2*M/R)+1
  let L := 4*M/R^2
  have hBJ : 1≤BJ := by
    have hh : 0≤C*(1+2*M/R) := mul_nonneg (by linarith) (by positivity)
    dsimp only [BJ]
    linarith
  have hBJpos : 0<BJ := lt_of_lt_of_le zero_lt_one hBJ
  have hL : 0≤L := by dsimp only [L];positivity
  let r := quantitativeNeumannRadius R BJ L
  have hrpos : 0<r := quantitativeNeumannRadius_pos hR hBJ hL
  have hrR : r≤R := min_le_left _ _
  let ρ := quantitativeInverseJointRadius r BJ L
  let δ := quantitativeInverseImageRadius r BJ L
  have hρ : 0<ρ := quantitativeInverseJointRadius_pos hrpos hBJpos hL
  have hδ : 0<δ := quantitativeInverseImageRadius_pos hrpos hBJpos hL
  have hρR : ρ≤R := (min_le_left _ _).trans (by linarith : r/2≤R)
  have hδρ : δ≤ρ := div_le_self hρ.le (by nlinarith : 1≤8*BJ)
  have hδ4R : δ≤4*R := by linarith
  refine ⟨N,Bpot,Dpot,ρ,δ,hN,hBpot,hDpot,hc,hρ,hδ,(ball_subset_ball hδ4R).trans hsource,?_⟩
  intro n hn
  let a0 := hillAbelianSelectedGlobalRootCoordinates q hq hr n hn
  let H := hillMixedSupportedPeriodMap q hq hr h0q h0r N n a0
  let J := hillSelectedMixedPeriodJointMap q hq hr h0q h0r N n hn
  let t0 : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2 := (0,SpectralWeight.one.toCoeff q)
  obtain ⟨hJ,hbound,hJ0,S,hQS0,hSQ0,hS⟩ := hdata n hn
  have hH : AnalyticOnNhd ℂ H (ball t0 (4*R)) := by
    intro t ht
    exact analyticAt_fst.comp (hJ t ht)
  have hH0 := hH t0 (mem_ball_self (by positivity : 0<4*R))
  let A := fderiv ℂ H t0
  have hA : ‖A‖≤2*M/R := by
    apply norm_fderiv_le_of_ball_bound H t0 t0 R R M hR
      (hH.differentiableOn.mono (ball_subset_ball (by linarith))) _ (mem_ball_self hR)
    intro t ht
    exact (show ‖H t‖≤‖J t‖ from le_max_left _ _).trans
      (hbound t (ball_subset_ball (by linarith : R+R≤4*R) ht))
  have hQ : A.comp (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2))=
      hillSelectedMixedPeriodJacobian q hq hr h0q h0r N n hn := by
    have hi : HasFDerivAt (fun b : PositiveDeletedCoeff 2 (n : ℤ) => (b,SpectralWeight.one.toCoeff q))
        (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2)) 0 :=
      hasFDerivAt_prodMk_left (0 : PositiveDeletedCoeff 2 (n : ℤ)) (SpectralWeight.one.toCoeff q)
    have hd := hH0.differentiableAt.hasFDerivAt.comp (0 : PositiveDeletedCoeff 2 (n : ℤ)) hi
    exact hd.fderiv.symm
  have hQS : (A.comp (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2))).comp S=ContinuousLinearMap.id ℂ _ := by
    rw [hQ]
    exact hQS0
  have hSQ : S.comp (A.comp (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2)))=ContinuousLinearMap.id ℂ _ := by
    rw [hQ]
    exact hSQ0
  obtain ⟨T,hT,hTB⟩ := exists_triangularLinearEquiv_norm_bound A S hQS hSQ
  have hDJ : fderiv ℂ J t0=A.prod (ContinuousLinearMap.snd ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2)) := by
    change fderiv ℂ (fun t => (H t,t.2)) t0=_
    simpa only [fderiv_snd] using hH0.differentiableAt.fderiv_prodMk differentiableAt_snd
  have hT' : (T : (PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) →L[ℂ]
      (PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2))=fderiv ℂ J t0 := hT.trans hDJ.symm
  have hTB' : ‖(T.symm : (PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) →L[ℂ]
      (PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2))‖≤BJ := by
    apply hTB.trans
    dsimp only [BJ]
    have hh : ‖S‖*(1+‖A‖)≤C*(1+2*M/R) := mul_le_mul hS (by linarith : 1+‖A‖≤1+2*M/R)
      (by positivity : 0≤1+‖A‖) (by linarith : 0≤C)
    linarith only [hh]
  have hLip (x : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) (hx : x∈ball t0 R)
      (y : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) (hy : y∈ball t0 R) :
      ‖fderiv ℂ J x-fderiv ℂ J y‖≤L*‖x-y‖ :=
    norm_fderiv_sub_le_of_holomorphic_ball_bound J t0 R M hR hJ.differentiableOn hbound hy hx
  obtain ⟨G,hGa,hG0,hG⟩ := exists_analytic_inverse_on_neumann_ball J t0 R BJ L hR hBJ hL
    (hJ.mono (ball_subset_ball (by linarith))) T hT' hTB' hLip
  change J t0=t0 at hJ0
  rw [hJ0] at hGa hG0 hG
  let s : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ) := fun p => (G (0,p)).1
  have hpair (p : Coeff 2) (hp : p∈ball (SpectralWeight.one.toCoeff q) δ) :
      ((0 : PositiveDeletedCoeff 2 (n : ℤ)),p)∈ball t0 δ := by
    rw [mem_ball]
    change max (dist (0 : PositiveDeletedCoeff 2 (n : ℤ)) 0) (dist p (SpectralWeight.one.toCoeff q))<δ
    rw [dist_self,max_eq_right dist_nonneg]
    exact hp
  refine ⟨s,?_,?_,?_⟩
  · intro p hp
    exact ((ContinuousLinearMap.fst ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2)).analyticAt _).comp
      ((hGa (0,p) (hpair p hp)).comp (f := fun p : Coeff 2 => ((0 : PositiveDeletedCoeff 2 (n : ℤ)),p))
        (analyticAt_const.prod analyticAt_id))
  · exact congrArg Prod.fst hG0
  · intro p hp
    obtain ⟨hmem,he,hunique⟩ := hG (0,p) (hpair p hp)
    have hsecond : (G (0,p)).2=p := congrArg Prod.snd he
    have hfirst : H (G (0,p))=0 := congrArg Prod.fst he
    have hsPair : (s p,p)=G (0,p) := Prod.ext rfl hsecond.symm
    refine ⟨by rw [hsPair];exact hmem,?_,?_⟩
    · rw [hsPair]
      exact hfirst
    · intro h hh hz
      have hroot : (h,p)∈ball t0 ρ := by
        rw [mem_ball]
        change max (dist h 0) (dist p (SpectralWeight.one.toCoeff q))<ρ
        exact max_lt_iff.mpr ⟨hh,(show dist p (SpectralWeight.one.toCoeff q)<δ from hp).trans_le hδρ⟩
      have hJroot : J (h,p)=(0,p) := Prod.ext hz rfl
      have hEq : (h,p)=G (0,p) := hunique (h,p) hroot hJroot
      exact congrArg Prod.fst hEq

/-- The actual common mixed roots have a linear source displacement
bound with constants and radii chosen before the differential index. -/
theorem exists_hillMixedSupportedPeriods_common_linear_root_bound :
    ∃ N : ℕ, ∃ B D ρ δ C : ℝ, 1≤N ∧ 0<B ∧ 0<D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
      0<ρ ∧ 0<δ ∧ 0<C ∧ ball (SpectralWeight.one.toCoeff q) δ⊆ball 0 B ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ s : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ),
        AnalyticOnNhd ℂ s (ball (SpectralWeight.one.toCoeff q) δ) ∧ s (SpectralWeight.one.toCoeff q)=0 ∧
        ∀ p∈ball (SpectralWeight.one.toCoeff q) δ,
          ‖s p‖≤C*‖p-SpectralWeight.one.toCoeff q‖ ∧
          (s p,p)∈ball (0,SpectralWeight.one.toCoeff q) ρ ∧
          hillMixedSupportedPeriodMap q hq hr h0q h0r N n (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn) (s p,p)=0 ∧
          ∀ h∈ball (0 : PositiveDeletedCoeff 2 (n : ℤ)) ρ,
            hillMixedSupportedPeriodMap q hq hr h0q h0r N n (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn) (h,p)=0 → h=s p := by
  obtain ⟨N,B,D,ρ,δ,hN,hB,hD,hc,hρ,hδ,hsource,hcharts⟩ :=
    exists_hillMixedSupportedPeriods_common_analytic_root q hq hr h0q h0r
  have hsub : ball (SpectralWeight.one.toCoeff q) (δ/4)⊆ball (SpectralWeight.one.toCoeff q) δ :=
    ball_subset_ball (by linarith)
  refine ⟨N,B,D,ρ,δ/4,8*ρ/δ,hN,hB,hD,hc,hρ,by positivity,by positivity,hsub.trans hsource,?_⟩
  intro n hn
  obtain ⟨s,ha,hzero,hinfo⟩ := hcharts n hn
  let p0 := SpectralWeight.one.toCoeff q
  let f : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ) := fun w => s (p0+w)
  have hshift (w : Coeff 2) : dist (p0+w) p0=‖w‖ := by
    rw [dist_eq_norm]
    congr 1
    abel
  have hf : AnalyticOnNhd ℂ f (ball 0 δ) := by
    intro w hw
    have hp : p0+w∈ball p0 δ := by
      rw [mem_ball,hshift]
      exact (show ‖w‖<δ by simpa only [mem_ball,dist_zero_right] using hw)
    exact (ha _ hp).comp (f := fun w : Coeff 2 => p0+w) (analyticAt_const.add analyticAt_id)
  have hfzero : f 0=0 := by simpa only [f,add_zero] using hzero
  have hfbound (w : Coeff 2) (hw : w∈ball 0 δ) : ‖f w‖≤ρ := by
    have hp : p0+w∈ball p0 δ := by
      rw [mem_ball,hshift]
      exact (show ‖w‖<δ by simpa only [mem_ball,dist_zero_right] using hw)
    have hmem := (hinfo (p0+w) hp).1
    have hh : ‖(s (p0+w),p0+w)-((0 : PositiveDeletedCoeff 2 (n : ℤ)),p0)‖<ρ := by
      simpa only [mem_ball,dist_eq_norm] using hmem
    have hfst : ‖s (p0+w)-0‖≤‖(s (p0+w),p0+w)-((0 : PositiveDeletedCoeff 2 (n : ℤ)),p0)‖ :=
      norm_fst_le ((s (p0+w),p0+w)-((0 : PositiveDeletedCoeff 2 (n : ℤ)),p0))
    simpa only [sub_zero] using hfst.trans hh.le
  refine ⟨s,ha.mono hsub,hzero,?_⟩
  intro p hp
  have hx : p-p0∈ball (0 : Coeff 2) (δ/4) := by
    simpa only [mem_ball,dist_zero_right,dist_eq_norm,sub_zero] using hp
  have hlin := norm_le_mul_norm_of_analytic_zero_ball_bound f δ ρ hδ hf hfzero hfbound (p-p0) hx
  have hback : p0+(p-p0)=p := by abel
  have hs : ‖s p‖≤(8*ρ/δ)*‖p-p0‖ := by simpa only [f,hback] using hlin
  exact ⟨hs,hinfo p (hsub hp)⟩

end NLS.KdV
