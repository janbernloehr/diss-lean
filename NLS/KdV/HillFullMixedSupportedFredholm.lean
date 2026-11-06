import NLS.KdV.HillFullMixedPeriodPhysical
import NLS.KdV.HillFullMixedPeriodCompact
import NLS.KdV.HillFullPeriodKernelInjectivity
import NLS.KdV.HillFullPeriodRootLimit
import NLS.SequenceSpaces.PositiveDeletedSpace
import NLS.SequenceSpaces.CompactIdentityFredholm

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillFullMixedSupportedPeriodMap (N : ℕ) (a : Coeff 2)
    (t : PositiveDeletedCoeff 2 (0 : ℤ) × Coeff 2) : PositiveDeletedCoeff 2 (0 : ℤ) :=
  Coeff.positiveDeletedProjectionTo 2 (0 : ℤ)
    (hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (a+(t.1 : Coeff 2),t.2))

theorem analyticOnNhd_hillFullMixedSupportedPeriodMap
    (N : ℕ) (a : Coeff 2) (U : Set (Coeff 2))
    (hF : AnalyticOnNhd ℂ (hillFullMixedComplexPeriodSequence q hq hr h0q h0r N) (univ ×ˢ U)) :
    AnalyticOnNhd ℂ (hillFullMixedSupportedPeriodMap q hq hr h0q h0r N a) (univ ×ˢ U) := by
  let inc : PositiveDeletedCoeff 2 (0 : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (0 : ℤ)).ker.subtypeL
  intro t ht
  have hJ : AnalyticAt ℂ (fun v : PositiveDeletedCoeff 2 (0 : ℤ) × Coeff 2 => (a+(v.1 : Coeff 2),v.2)) t :=
    (analyticAt_const.add ((inc.analyticAt t.1).comp (f := fun v : PositiveDeletedCoeff 2 (0 : ℤ) × Coeff 2 => v.1)
      analyticAt_fst)).prod analyticAt_snd
  have hG := (hF (a+(t.1 : Coeff 2),t.2) ⟨mem_univ _,ht.2⟩).comp
    (f := fun v : PositiveDeletedCoeff 2 (0 : ℤ) × Coeff 2 => (a+(v.1 : Coeff 2),v.2)) hJ
  exact ((Coeff.positiveDeletedProjectionTo 2 (0 : ℤ)).analyticAt _).comp hG

theorem hillFullMixedSupportedPeriodMap_base_coordinate
    (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B)
    (a : Coeff 2) (b : PositiveDeletedCoeff 2 (0 : ℤ)) :
    (hillFullMixedSupportedPeriodMap q hq hr h0q h0r N a (b,SpectralWeight.one.toCoeff q) : Coeff 2) (k : ℤ) =
      (-2*(Real.pi : ℂ))*hillAbelianProductComplexPeriod q hq hr 0 k (a+(b : Coeff 2),SpectralWeight.one.toCoeff q) := by
  rw [hillFullMixedSupportedPeriodMap,Coeff.positiveDeletedProjectionTo_coe,Coeff.positiveDeletedProjection_apply,
    if_pos (show (0 : ℤ) < k ∧ (k : ℤ) ≠ 0 by constructor <;> omega),
    hillFullMixedComplexPeriodSequence_at_base_coordinate q hq hr h0q h0r N k hN hk B D hD hc hp]

theorem hillFullMixedSupportedPeriodMap_root_derivative_kernel_eq_zero
    (N : ℕ) (hN : 1 ≤ N) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hdiff : DifferentiableAt ℂ
      (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => hillFullMixedSupportedPeriodMap q hq hr h0q h0r N
        (hillGapRootHilbertCoordinates q hq hr roots hroots) (b,SpectralWeight.one.toCoeff q)) 0)
    (h : PositiveDeletedCoeff 2 (0 : ℤ))
    (hker : fderiv ℂ
      (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => hillFullMixedSupportedPeriodMap q hq hr h0q h0r N
        (hillGapRootHilbertCoordinates q hq hr roots hroots) (b,SpectralWeight.one.toCoeff q)) 0 h = 0) : h = 0 := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  let G := fun b : PositiveDeletedCoeff 2 (0 : ℤ) =>
    hillFullMixedSupportedPeriodMap q hq hr h0q h0r N a (b,SpectralWeight.one.toCoeff q)
  let T := fderiv ℂ G 0
  let inc : PositiveDeletedCoeff 2 (0 : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (0 : ℤ)).ker.subtypeL
  apply Subtype.ext
  change (h : Coeff 2)=0
  apply hillAbelianFullProductPeriod_root_derivative_kernel_eq_zero q hq hr h0q h0r roots hroots (h : Coeff 2)
  · intro m hm
    have he := congrArg (fun v : Coeff 2 => v m) (Coeff.positiveDeleted_fixed 2 (0 : ℤ) h)
    rw [Coeff.positiveDeletedProjection_apply,if_neg (by omega : ¬(0<m ∧ m≠0))] at he
    exact he.symm
  · intro k hk
    let c : ℂ := -2*(Real.pi : ℂ)
    let ev : PositiveDeletedCoeff 2 (0 : ℤ) →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)).comp inc
    have he : (fun b => ev (G b)) = (fun b : PositiveDeletedCoeff 2 (0 : ℤ) =>
        c*hillAbelianProductComplexPeriod q hq hr 0 k (a+(b : Coeff 2),SpectralWeight.one.toCoeff q)) :=
      funext (fun b => hillFullMixedSupportedPeriodMap_base_coordinate q hq hr h0q h0r N k hN hk B D hD hc hp a b)
    have hE := ev.hasFDerivAt.comp (0 : PositiveDeletedCoeff 2 (0 : ℤ)) hdiff.hasFDerivAt
    have hinc : HasFDerivAt (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => a+(b : Coeff 2)) inc 0 :=
      inc.hasFDerivAt.const_add a
    obtain ⟨U,C,_,hqU,_,hA,_⟩ := exists_hillAbelianProductComplexPeriod_full_uniform_bound q hq hr k hk 0 (by norm_num)
    have hPa : AnalyticAt ℂ (fun b : Coeff 2 =>
        hillAbelianProductComplexPeriod q hq hr 0 k (b,SpectralWeight.one.toCoeff q)) a :=
      (hA 0 (a,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqU⟩).comp
        (f := fun b : Coeff 2 => (b,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
    have hP : HasFDerivAt (fun b : Coeff 2 => hillAbelianProductComplexPeriod q hq hr 0 k (b,SpectralWeight.one.toCoeff q))
        (fderiv ℂ (fun b : Coeff 2 => hillAbelianProductComplexPeriod q hq hr 0 k (b,SpectralWeight.one.toCoeff q)) a)
        (a+((0 : PositiveDeletedCoeff 2 (0 : ℤ)) : Coeff 2)) := by
      simpa only [ZeroMemClass.coe_zero,add_zero] using hPa.differentiableAt.hasFDerivAt
    have hknown := (hP.comp (f := fun b : PositiveDeletedCoeff 2 (0 : ℤ) => a+(b : Coeff 2)) 0 hinc).const_mul c
    change HasFDerivAt (fun b => ev (G b)) (ev.comp T) 0 at hE
    rw [he] at hE
    have hv := congrArg (fun L : PositiveDeletedCoeff 2 (0 : ℤ) →L[ℂ] ℂ => L h) (hE.unique hknown)
    have hkerT : T h = 0 := hker
    have hcz : c ≠ 0 := mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hincval : inc h = (h : Coeff 2) := rfl
    have hz : c*(fderiv ℂ (fun b : Coeff 2 => hillAbelianProductComplexPeriod q hq hr 0 k (b,SpectralWeight.one.toCoeff q)) a
        (h : Coeff 2)) = 0 := by
      simpa only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,hkerT,map_zero,hincval] using hv.symm
    exact (mul_eq_zero.mp hz).resolve_left hcz

theorem isCompactOperator_fderiv_hillFullMixedSupportedPeriodMap_add_id
    (N : ℕ) (hN : 1 ≤ N) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (a p : Coeff 2) (hp : ‖p‖ ≤ B)
    (hF : AnalyticOnNhd ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)) univ) :
    IsCompactOperator (fderiv ℂ
      (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => hillFullMixedSupportedPeriodMap q hq hr h0q h0r N a (b,p)) 0+
        ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (0 : ℤ))) := by
  let inc : PositiveDeletedCoeff 2 (0 : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (0 : ℤ)).ker.subtypeL
  let P := Coeff.positiveDeletedProjectionTo 2 (0 : ℤ)
  let T := fderiv ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)) a
  have hinc : HasFDerivAt (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => a+(b : Coeff 2)) inc 0 :=
    inc.hasFDerivAt.const_add a
  have hG : HasFDerivAt (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)) T
      (a+((0 : PositiveDeletedCoeff 2 (0 : ℤ)) : Coeff 2)) := by
    simpa only [ZeroMemClass.coe_zero,add_zero] using (hF a (mem_univ _)).differentiableAt.hasFDerivAt
  have hd := P.hasFDerivAt.comp (0 : PositiveDeletedCoeff 2 (0 : ℤ))
    (hG.comp (f := fun b : PositiveDeletedCoeff 2 (0 : ℤ) => a+(b : Coeff 2)) 0 hinc)
  have hder : fderiv ℂ
      (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => hillFullMixedSupportedPeriodMap q hq hr h0q h0r N a (b,p)) 0 =
        P.comp (T.comp inc) := by
    convert! hd.fderiv using 1
  have hcompact := isCompactOperator_fderiv_hillFullMixedPeriod_add_projection q hq hr h0q h0r N hN B D hD hc a p hp hF
  have hc' : IsCompactOperator (P.comp ((T+Coeff.positiveDeletedProjection 2 (0 : ℤ)).comp inc)) := by
    exact (hcompact.comp_clm inc).clm_comp P
  have he : fderiv ℂ
      (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => hillFullMixedSupportedPeriodMap q hq hr h0q h0r N a (b,p)) 0+
        ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (0 : ℤ)) =
      P.comp ((T+Coeff.positiveDeletedProjection 2 (0 : ℤ)).comp inc) := by
    rw [hder]
    apply ContinuousLinearMap.ext
    intro b
    apply Subtype.ext
    change Coeff.positiveDeletedProjection 2 (0 : ℤ) (T (b : Coeff 2))+(b : Coeff 2) =
      Coeff.positiveDeletedProjection 2 (0 : ℤ) (T (b : Coeff 2)+Coeff.positiveDeletedProjection 2 (0 : ℤ) b)
    rw [map_add,Coeff.positiveDeletedProjection_idempotent,Coeff.positiveDeleted_fixed]
  rw [he]
  exact hc'

theorem hillFullMixedSupportedPeriodMap_root_derivative_bijective
    (N : ℕ) (hN : 1 ≤ N) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hF : AnalyticOnNhd ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N
      (b,SpectralWeight.one.toCoeff q)) univ) :
    Function.Bijective (fderiv ℂ
      (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => hillFullMixedSupportedPeriodMap q hq hr h0q h0r N
        (hillGapRootHilbertCoordinates q hq hr roots hroots) (b,SpectralWeight.one.toCoeff q)) 0) := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  let G := fun b : PositiveDeletedCoeff 2 (0 : ℤ) => hillFullMixedSupportedPeriodMap q hq hr h0q h0r N a
    (b,SpectralWeight.one.toCoeff q)
  let T := fderiv ℂ G 0
  have hcompact : IsCompactOperator (T+ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (0 : ℤ))) :=
    isCompactOperator_fderiv_hillFullMixedSupportedPeriodMap_add_id q hq hr h0q h0r N hN B D hD hc a _ hp hF
  let inc : PositiveDeletedCoeff 2 (0 : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (0 : ℤ)).ker.subtypeL
  have hinc : AnalyticAt ℂ (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => a+(b : Coeff 2)) 0 :=
    analyticAt_const.add (inc.analyticAt 0)
  have hGa : AnalyticAt ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N
      (b,SpectralWeight.one.toCoeff q)) (a+((0 : PositiveDeletedCoeff 2 (0 : ℤ)) : Coeff 2)) := by
    simpa only [ZeroMemClass.coe_zero,add_zero] using hF a (mem_univ _)
  have hG : AnalyticAt ℂ G 0 := ((Coeff.positiveDeletedProjectionTo 2 (0 : ℤ)).analyticAt _).comp
    (hGa.comp (f := fun b : PositiveDeletedCoeff 2 (0 : ℤ) => a+(b : Coeff 2)) hinc)
  have hinj : Function.Injective T := by
    intro x y he
    have hz : T (x-y)=0 := by rw [map_sub,he,sub_self]
    exact sub_eq_zero.mp (hillFullMixedSupportedPeriodMap_root_derivative_kernel_eq_zero q hq hr h0q h0r
      N hN B D hD hc hp roots hroots hG.differentiableAt (x-y) hz)
  have he : -(ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (0 : ℤ)))+
      (T+ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (0 : ℤ))) = T := by abel
  have hbijD : Function.Bijective (-(ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (0 : ℤ)))) := by
    change Function.Bijective (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => -b)
    exact neg_bijective
  have hbij := Coeff.bijective_add_compact_of_bijective_of_injective
    (-(ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (0 : ℤ))))
    (T+ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (0 : ℤ))) hbijD hcompact
    (by rw [he];exact hinj)
  rw [he] at hbij
  exact hbij


/-- One original complex source neighborhood supports the actual full
period map and its invertible positive-root derivative at every real
vector in the original gap box. -/
theorem exists_hillFullMixedSupportedPeriodMap_Fredholm_neighborhood :
    ∃ N : ℕ, ∃ B D : ℝ, ∃ U : Set (Coeff 2),
      1 ≤ N ∧ 0 < B ∧ 0 < D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
        IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧ U ⊆ ball 0 B ∧
          AnalyticOnNhd ℂ (hillFullMixedComplexPeriodSequence q hq hr h0q h0r N) (univ ×ˢ U) ∧
          (∀ a : Coeff 2, AnalyticOnNhd ℂ (hillFullMixedSupportedPeriodMap q hq hr h0q h0r N a) (univ ×ˢ U)) ∧
          ∀ roots : ℕ → ℝ, ∀ hroots : roots ∈ hillGapRootBox q hq hr,
            Function.Bijective (fderiv ℂ
              (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => hillFullMixedSupportedPeriodMap q hq hr h0q h0r N
                (hillGapRootHilbertCoordinates q hq hr roots hroots) (b,SpectralWeight.one.toCoeff q)) 0) := by
  obtain ⟨N,B,D,U,hN,hB,hD,hc,hU,hqU,hsub,hF⟩ :=
    exists_hillFullMixedComplexPeriodSequence_analytic_neighborhood q hq hr h0q h0r
  have hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B := by
    have hh := hsub hqU
    exact (show ‖SpectralWeight.one.toCoeff q‖<B by simpa only [mem_ball,dist_zero_right] using hh).le
  have hsec : AnalyticOnNhd ℂ (fun b : Coeff 2 =>
      hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) univ := by
    intro a _
    exact (hF (a,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqU⟩).comp
      (f := fun b : Coeff 2 => (b,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  exact ⟨N,B,D,U,hN,hB,hD,hc,hU,hqU,hsub,hF,
    fun a => analyticOnNhd_hillFullMixedSupportedPeriodMap q hq hr h0q h0r N a U hF,
    fun roots hroots => hillFullMixedSupportedPeriodMap_root_derivative_bijective q hq hr h0q h0r
      N hN B D hD.le hc hp roots hroots hsec⟩

/-- The original selected root subsequence supplies a zero of the actual
full Hilbert period map, with a bijective positive-root derivative. -/
theorem exists_hillFullMixedSupportedPeriodMap_regular_zero :
    ∃ N : ℕ, ∃ U : Set (Coeff 2), ∃ roots : hillGapRootBox q hq hr,
      IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧
        AnalyticOnNhd ℂ (hillFullMixedSupportedPeriodMap q hq hr h0q h0r N
          (hillGapRootHilbertCoordinates q hq hr roots.val roots.property)) (univ ×ˢ U) ∧
        hillFullMixedSupportedPeriodMap q hq hr h0q h0r N
          (hillGapRootHilbertCoordinates q hq hr roots.val roots.property) (0,SpectralWeight.one.toCoeff q)=0 ∧
        Function.Bijective (fderiv ℂ
          (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => hillFullMixedSupportedPeriodMap q hq hr h0q h0r N
            (hillGapRootHilbertCoordinates q hq hr roots.val roots.property) (b,SpectralWeight.one.toCoeff q)) 0) := by
  obtain ⟨N,B,D,U,hN,_,hD,hc,hU,hqU,hsub,_,hA,hbij⟩ :=
    exists_hillFullMixedSupportedPeriodMap_Fredholm_neighborhood q hq hr h0q h0r
  obtain ⟨roots,φ,_,_,hperiods⟩ := exists_hillAbelianSelectedGlobalRoots_full_product_subsequence q hq hr
  have hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B := by
    have hh := hsub hqU
    exact (show ‖SpectralWeight.one.toCoeff q‖<B by simpa only [mem_ball,dist_zero_right] using hh).le
  refine ⟨N,U,roots,hU,hqU,hA _,?_,hbij roots.val roots.property⟩
  rw [hillFullMixedSupportedPeriodMap]
  simp only [ZeroMemClass.coe_zero,add_zero]
  rw [hillFullMixedComplexPeriodSequence_at_full_period_roots_eq_zero q hq hr h0q h0r N hN B D hD.le hc hp _ ?_,map_zero]
  intro k hk
  rw [hillAbelianProductComplexPeriod_at_base q hq hr 0 k hk]
  exact hperiods k hk

theorem hillFullMixedSupportedPeriodMap_partial_derivative_bijective
    (N : ℕ) (hN : 1 ≤ N) (B D : ℝ)
    (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hF : AnalyticAt ℂ (hillFullMixedSupportedPeriodMap q hq hr h0q h0r N
      (hillGapRootHilbertCoordinates q hq hr roots hroots)) (0,SpectralWeight.one.toCoeff q))
    (hsec : AnalyticOnNhd ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N
      (b,SpectralWeight.one.toCoeff q)) univ) :
    Function.Bijective ((fderiv ℂ (hillFullMixedSupportedPeriodMap q hq hr h0q h0r N
      (hillGapRootHilbertCoordinates q hq hr roots hroots)) (0,SpectralWeight.one.toCoeff q)).comp
        (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (0 : ℤ)) (Coeff 2))) := by
  let F := hillFullMixedSupportedPeriodMap q hq hr h0q h0r N (hillGapRootHilbertCoordinates q hq hr roots hroots)
  have hi : HasFDerivAt (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => (b,SpectralWeight.one.toCoeff q))
      (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (0 : ℤ)) (Coeff 2)) 0 :=
    hasFDerivAt_prodMk_left (0 : PositiveDeletedCoeff 2 (0 : ℤ)) (SpectralWeight.one.toCoeff q)
  have hd : HasFDerivAt (fun b : PositiveDeletedCoeff 2 (0 : ℤ) => F (b,SpectralWeight.one.toCoeff q))
      ((fderiv ℂ F (0,SpectralWeight.one.toCoeff q)).comp
        (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (0 : ℤ)) (Coeff 2))) 0 := by
    convert! hF.differentiableAt.hasFDerivAt.comp
      (f := fun b : PositiveDeletedCoeff 2 (0 : ℤ) => (b,SpectralWeight.one.toCoeff q))
      (0 : PositiveDeletedCoeff 2 (0 : ℤ)) hi using 1
  rw [← hd.fderiv]
  exact hillFullMixedSupportedPeriodMap_root_derivative_bijective q hq hr h0q h0r N hN B D hD hc hp
    roots hroots hsec

end NLS.KdV
