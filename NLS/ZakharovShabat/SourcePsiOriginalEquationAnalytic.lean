import NLS.ZakharovShabat.SourcePsiOriginalEquation
import NLS.ZakharovShabat.SourcePsiComplexContourAnalytic
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-!
# Analyticity of the original lp-valued psi equation

Fixed original circles give analytic scalar coordinates near each complex
source. The proved sequence bounds promote these to Banach analyticity.
Agreement on overlapping contour families yields one map on all of W.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceCorollary10_6Data.originalEquation_analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    (hInt : ∀ n : ℤ, IsOpen (sourcePsiContourJointDomain hp hp1 W) ∧
      AnalyticOnNhd ℂ (sourcePsiContourIntegrandJoint hp hp1 n) (sourcePsiContourJointDomain hp hp1 W))
    (n : ℤ) :
    AnalyticOnNhd ℂ (fun t : DeletedCoeff p n × CoeffPair p => sourcePsiOriginalEquation hp hp1 n t.1 t.2)
      (univ ×ˢ W) := by
  intro t ht
  obtain ⟨V,hV,_,hφV,_,D,c,hD⟩ := H.neighborhoods t.2 ht.2
  choose d r hr he using hD.discs
  obtain ⟨U₀,hU₀,hbase,hUW,C,_,hb⟩ := H.originalEquation_uniformNorm hW t.2 ht.2 (t.1:Coeff p)
  let inc : DeletedCoeff p n × CoeffPair p → Coeff p × CoeffPair p := fun q => ((q.1:Coeff p),q.2)
  have hic : Continuous inc := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hia (q : DeletedCoeff p n × CoeffPair p) : AnalyticAt ℂ inc q :=
    (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL.analyticAt q.1).comp analyticAt_fst).prod analyticAt_snd
  let U := inc ⁻¹' U₀ ∩ (univ ×ˢ V)
  have hU : IsOpen U := (hU₀.preimage hic).inter (isOpen_univ.prod hV)
  have htU : t ∈ U := ⟨hbase,mem_univ _,hφV⟩
  let F : DeletedCoeff p n × CoeffPair p → Coeff p := fun q => (sourcePsiOriginalEquation hp hp1 n q.1 q.2:Coeff p)
  have hcoord (m : ℤ) : AnalyticOnNhd ℂ (fun q => F q m) U := by
    have hraw : AnalyticOnNhd ℂ (fun q : DeletedCoeff p n × CoeffPair p =>
        sourcePsiEquationCoordinate hp hp1 n m (q.1:Coeff p) q.2 (d m:ℂ) (r m)) U := by
      intro q hq
      let P := hD.toSourceIsolatingNeighborhoods.periodCircle q.2 hq.2.2 m (d m) (r m) (hr m) (he m)
      exact (analyticAt_sourcePsiEquationCoordinate_of_contour_domain hp hp1 n m (q.1:Coeff p) q.2
        (d m:ℂ) (r m) (hr m).le W (hUW hq.1).2 (hInt n).1 (hInt n).2 P.sphere_subset_rootDomain).comp
          (f := inc) (hia q)
    apply hraw.congr hU
    intro q hq
    let P := hD.toSourceIsolatingNeighborhoods.periodCircle q.2 hq.2.2 m (d m) (r m) (hr m) (he m)
    exact (H.originalEquation_apply hW q.2 (hUW hq.1).2 n q.1 m P).symm
  have hF : AnalyticOnNhd ℂ F U := Coeff.analyticOnNhd_of_bounded_coordinatewise F hU hcoord C
    (fun q hq => hb n q.1 q.2 hq.1)
  have hproject := (Coeff.deleteCoordinateTo (p := p) n).comp_analyticOnNhd hF
  change AnalyticOnNhd ℂ (fun q => Coeff.deleteCoordinateTo n (F q)) U at hproject
  have he : (fun q => Coeff.deleteCoordinateTo n (F q)) =
      (fun q : DeletedCoeff p n × CoeffPair p => sourcePsiOriginalEquation hp hp1 n q.1 q.2) := by
    funext q
    apply Subtype.ext
    exact (Coeff.deleteCoordinate_eq_self_iff n _).mpr (sourcePsiOriginalEquation hp hp1 n q.1 q.2).property
  rw [he] at hproject
  exact hproject t htU

/-- The source-first parameter order printed in Lemma 12.4. -/
theorem SourceCorollary10_6Data.originalEquation_analytic_sourceFirst
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    (hInt : ∀ n : ℤ, IsOpen (sourcePsiContourJointDomain hp hp1 W) ∧
      AnalyticOnNhd ℂ (sourcePsiContourIntegrandJoint hp hp1 n) (sourcePsiContourJointDomain hp hp1 W))
    (n : ℤ) :
    AnalyticOnNhd ℂ (fun t : CoeffPair p × DeletedCoeff p n => sourcePsiOriginalEquation hp hp1 n t.2 t.1)
      (W ×ˢ univ) := by
  intro t ht
  exact (H.originalEquation_analytic hW hInt n (t.2,t.1) ⟨mem_univ _,ht.1⟩).comp
    (f := fun q : CoeffPair p × DeletedCoeff p n => (q.2,q.1)) (analyticAt_snd.prod analyticAt_fst)

end NLS.ZakharovShabat
