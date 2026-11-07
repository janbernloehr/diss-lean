import NLS.ComplexAnalysis.RealAnalyticNeighborhoodExtension

/-! Compatible Banach-valued analytic charts on real-centered balls.
The balls can be chosen once for a family of target exponents. -/
noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.ComplexAnalysis.ContractiveComplexification
variable {R E F : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem real_projection_ball (c : ContractiveComplexification R E)
    (hnorm : ∀ x, ‖c.inclusion x‖=‖x‖) (a : R) (r : ℝ) {z : E}
    (hz : z ∈ ball (c.inclusion a) r) :
    c.inclusion (c.re z) ∈ ball (c.inclusion a) r := by
  rw [mem_ball,dist_eq_norm,← map_sub,hnorm]
  have he : c.re z-a=c.re (z-c.inclusion a) := by rw [map_sub,c.re_inclusion]
  rw [he]
  exact (c.norm_re _).trans_lt (by simpa only [mem_ball,dist_eq_norm] using hz)

theorem complex_ball_extensions_agree (c : ContractiveComplexification R E)
    (hnorm : ∀ x, ‖c.inclusion x‖=‖x‖) (f : R → F)
    (g h : E → F) (a b : R) (r s : ℝ)
    (hg : AnalyticOnNhd ℂ g (ball (c.inclusion a) r))
    (hh : AnalyticOnNhd ℂ h (ball (c.inclusion b) s))
    (hga : ∀ y : R, c.inclusion y ∈ ball (c.inclusion a) r → g (c.inclusion y)=f y)
    (hhb : ∀ y : R, c.inclusion y ∈ ball (c.inclusion b) s → h (c.inclusion y)=f y) :
    EqOn g h (ball (c.inclusion a) r ∩ ball (c.inclusion b) s) := by
  intro z hz
  let U := ball (c.inclusion a) r ∩ ball (c.inclusion b) s
  have hφ : c.inclusion (c.re z) ∈ U :=
    ⟨real_projection_ball c hnorm a r hz.1,real_projection_ball c hnorm b s hz.2⟩
  have hzero := AnalyticOnNhd.eqOn_zero_of_continuous_real_form
    (range c.inclusion)
    (by rintro x y ⟨u,rfl⟩ ⟨v,rfl⟩; exact ⟨u+v,map_add _ _ _⟩)
    (by intro t x hx; obtain ⟨u,rfl⟩ := hx; exact ⟨t • u,by rw [map_smul,Complex.coe_smul]⟩)
    (fun v => c.inclusion (c.re v)) (fun v => c.inclusion (c.im v))
    (fun v => ⟨c.re v,rfl⟩) (fun v => ⟨c.im v,rfl⟩) (fun v => (c.decomposition v).symm)
    (c.inclusion.continuous.comp c.re.continuous).continuousAt (by rw [map_zero,map_zero])
    (c.inclusion.continuous.comp c.im.continuous).continuousAt (by rw [map_zero,map_zero])
    U (isOpen_ball.inter isOpen_ball) ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    ⟨c.inclusion (c.re z),hφ,⟨c.re z,rfl⟩⟩ (fun x => g x-h x)
    (fun x hx => (hg x hx.1).sub (hh x hx.2))
    (by
      rintro x hx ⟨y,rfl⟩
      rw [hga y hx.1,hhb y hx.2,sub_self])
  exact sub_eq_zero.mp (hzero hz)

theorem exists_complex_extension_on_given_balls (c : ContractiveComplexification R E)
    (hnorm : ∀ x, ‖c.inclusion x‖=‖x‖) (f : R → F)
    (g : R → E → F) (r : R → ℝ) (hr : ∀ x, 0 < r x)
    (hg : ∀ x, AnalyticOnNhd ℂ (g x) (ball (c.inclusion x) (r x)))
    (hreal : ∀ x y : R, c.inclusion y ∈ ball (c.inclusion x) (r x) →
      g x (c.inclusion y)=f y) :
    ∃ H : E → F, AnalyticOnNhd ℂ H (⋃ x : R, ball (c.inclusion x) (r x)) ∧
      (∀ x : R, H (c.inclusion x)=f x) ∧
      ∀ x : R, EqOn H (g x) (ball (c.inclusion x) (r x)) := by
  classical
  let U := ⋃ x : R, ball (c.inclusion x) (r x)
  let H : E → F := fun z => if hz : z ∈ U then g (Classical.choose (mem_iUnion.mp hz)) z else 0
  have heq (x : R) : EqOn H (g x) (ball (c.inclusion x) (r x)) := by
    intro z hz
    have hzU : z ∈ U := mem_iUnion.mpr ⟨x,hz⟩
    change (if h : z ∈ U then g (Classical.choose (mem_iUnion.mp h)) z else 0)=g x z
    rw [dif_pos hzU]
    exact complex_ball_extensions_agree c hnorm f _ _ _ _ _ _
      (hg _) (hg x) (hreal _) (hreal x) ⟨Classical.choose_spec (mem_iUnion.mp hzU),hz⟩
  refine ⟨H,?_,?_,heq⟩
  · intro z hz
    obtain ⟨x,hx⟩ := mem_iUnion.mp hz
    apply (hg x z hx).congr
    filter_upwards [isOpen_ball.mem_nhds hx] with w hw
    exact (heq x hw).symm
  · intro x
    exact (heq x (mem_ball_self (hr x))).trans (hreal x x (mem_ball_self (hr x)))

end NLS.ComplexAnalysis.ContractiveComplexification
