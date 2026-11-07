import NLS.KdV.HillHminusOneCanonicalRealActions
import NLS.KdV.HillHminusOneMiuraCanonicalActionFamilies
import NLS.SequenceSpaces.PeriodOneHminusOneRealForm

/-! # Common Miura action balls and agreement on every complex overlap

Each ball has a real center, an actual analytic real-preserving Miura
lift and an energy shift outside every source spectrum in that ball.
ALL positive indexed actions are analytic on that SAME ball. The real
boundary-integral identity and the physical real form prove agreement
on the WHOLE overlap of any two such balls, simultaneously at all indices.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.KdV

structure HillHminusMiuraActionBall where
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  radius : ℝ
  radius_pos : 0 < radius
  shift : ℝ
  lift : PeriodOneHminusOne → Coeff 2
  lift_analytic : AnalyticOnNhd ℂ lift (ball center radius)
  lift_real : ∀ q ∈ ball center radius, IsRealPeriodOneHminusOne q →
    ∀ k : ℤ, lift q (-k) = star (lift q k)
  image : ∀ q ∈ ball center radius, periodOneMiura (lift q) =
    q+periodOneL2Inclusion (lp.single 2 0 (shift : ℂ))
  outside : ∀ q ∈ ball center radius, -(shift : ℂ) ∉ singularHillSpectrum (periodOneOriginal q)
  action_analytic : ∀ n : ℕ+, AnalyticOnNhd ℂ
    (fun q => hillHminusMiuraIndexedAction (lift q) (n : ℕ)) (ball center radius)

namespace HillHminusMiuraActionBall

def source (B : HillHminusMiuraActionBall) : Set PeriodOneHminusOne := ball B.center B.radius
def action (B : HillHminusMiuraActionBall) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  hillHminusMiuraIndexedAction (B.lift q) (n : ℕ)

theorem source_open (B : HillHminusMiuraActionBall) : IsOpen B.source := isOpen_ball

theorem analytic_action (B : HillHminusMiuraActionBall) (n : ℕ+) :
    AnalyticOnNhd ℂ (B.action n) B.source := B.action_analytic n

theorem action_eq_canonical_real (B : HillHminusMiuraActionBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hreal : IsRealPeriodOneHminusOne q) :
    B.action n q = hillHminusCanonicalRealAction q hreal n := by
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hq hreal⟩
  exact hillHminusMiuraIndexedAction_eq_canonicalRealAction q hreal u B.shift (B.image q hq) (B.outside q hq) n

theorem action_eq_on_overlap (B C : HillHminusMiuraActionBall) (n : ℕ+) :
    EqOn (B.action n) (C.action n) (B.source ∩ C.source) := by
  intro q hq
  have hreal : ∃ a ∈ B.source ∩ C.source, IsRealPeriodOneHminusOne a :=
    exists_real_mem_periodOneHminus_ball_inter B.center C.center B.center_real C.center_real
      B.radius C.radius ⟨q,hq⟩
  have he := analytic_eqOn_of_real_periodOneHminus (B.source ∩ C.source)
    (B.source_open.inter C.source_open) ((convex_ball B.center B.radius).inter
      (convex_ball C.center C.radius)).isPreconnected hreal (B.action n) (C.action n)
    ((B.analytic_action n).mono inter_subset_left) ((C.analytic_action n).mono inter_subset_right)
    (fun a ha har => (B.action_eq_canonical_real n a ha.1 har).trans
      (C.action_eq_canonical_real n a ha.2 har).symm)
  exact he hq

end HillHminusMiuraActionBall

theorem exists_hillHminusMiuraActionBall (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ B : HillHminusMiuraActionBall, q ∈ B.source := by
  obtain ⟨c,_,_,V,hV,hqV,u,hu,hreal,himage,hacts,houtside,_,_⟩ :=
    exists_hillHminus_Miura_action_family_outside_spectrum q hq 0
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hqV)
  let B : HillHminusMiuraActionBall := {
    center := q
    center_real := hq
    radius := r
    radius_pos := hr
    shift := c^2
    lift := u
    lift_analytic := hu.mono hball
    lift_real := fun a ha har => hreal a (hball ha) har
    image := fun a ha => by simpa only [ofReal_pow] using himage a (hball ha)
    outside := fun a ha => by simpa only [ofReal_pow] using houtside a (hball ha)
    action_analytic := fun n => (hacts (n : ℕ)).mono hball }
  refine ⟨B,?_⟩
  change q ∈ ball q r
  exact mem_ball_self hr

end NLS.KdV
