module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! In the coordinate r = sin θ the branch denominator disappears from the
Laplace differential. The two determinations of the cut lie at π/2 ± iy. -/
public section
namespace CubicTheta
open Complex Filter MeasureTheory
open scoped Topology
noncomputable section

def stripKernel (z ν : ℝ) (θ : ℂ) : ℂ :=
  exp (-(z : ℂ) * sin θ) * cos ((ν : ℂ) * θ)

theorem stripKernel_entire (z ν : ℝ) : Differentiable ℂ (stripKernel z ν) := by
  unfold stripKernel
  fun_prop

/-- The Jacobian from r=sin θ removes the apparent pole in the kernel. -/
theorem strip_pullback (z ν : ℝ) (θ : ℂ) (h : cos θ ≠ 0) :
    exp (-(z : ℂ) * sin θ) * (cos ((ν : ℂ) * θ) / cos θ) * cos θ =
    stripKernel z ν θ := by
  unfold stripKernel
  field_simp

/-- The exact upper-minus-lower integrand. The factor I comes from the
orientations of the two vertical sides in θ. -/
theorem cut_pair (z ν y : ℝ) :
    stripKernel z ν (↑(Real.pi/2) + y*I) +
    stripKernel z ν (↑(Real.pi/2) + ↑(-y)*I) =
    ↑(2 * Real.cos (ν*(Real.pi/2)) * Real.exp (-z*Real.cosh y) * Real.cosh (ν*y)) := by
  have hs (v : ℝ) : sin (↑(Real.pi/2) + v*I) = (Real.cosh v : ℂ) := by
    rw [sin_add, ← ofReal_sin, ← ofReal_cos, Real.sin_pi_div_two, Real.cos_pi_div_two]
    simp [cos_mul_I]
  unfold stripKernel
  rw [hs,hs,Real.cosh_neg, ← mul_add, cos_add_cos]
  have ha : ((ν : ℂ)*(↑(Real.pi/2) + y*I) + ν*(↑(Real.pi/2) + ↑(-y)*I))/2 =
      ↑(ν*(Real.pi/2)) := by push_cast; ring
  have hb : ((ν : ℂ)*(↑(Real.pi/2) + y*I) - ν*(↑(Real.pi/2) + ↑(-y)*I))/2 =
      ↑(ν*y)*I := by push_cast; ring
  rw [ha,hb,cos_mul_I]
  push_cast
  ring

def vertical (z ν a l h : ℝ) : ℂ :=
  I * ∫ y : ℝ in l..h, stripKernel z ν (a+y*I)

def connector (z ν a b y : ℝ) : ℂ :=
  ∫ x : ℝ in a..b, stripKernel z ν (x+y*I)

/-- Finite contour deformation; the only errors are the two remote connectors. -/
theorem strip_rectangle (z ν a b Y : ℝ) :
    vertical z ν a (-Y) Y = vertical z ν b (-Y) Y +
      connector z ν a b (-Y) - connector z ν a b Y := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (stripKernel z ν)
    (⟨a,-Y⟩ : ℂ) (⟨b,Y⟩ : ℂ) (stripKernel_entire z ν).differentiableOn
  simp only [smul_eq_mul] at h
  unfold vertical connector
  linear_combination -h

theorem vertical_cut (z ν Y : ℝ) :
    vertical z ν (Real.pi/2) (-Y) Y =
    I * ∫ y : ℝ in 0..Y,
      (↑(2 * Real.cos (ν*(Real.pi/2)) * Real.exp (-z*Real.cosh y) * Real.cosh (ν*y)) : ℂ) := by
  let f := fun y : ℝ ↦ stripKernel z ν (↑(Real.pi/2) + y*I)
  have hf : Continuous f := (stripKernel_entire z ν).continuous.comp (by fun_prop)
  unfold vertical
  change I * (∫ y in -Y..Y, f y) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-Y) 0) (hf.intervalIntegrable 0 Y)]
  have hneg := intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := Y)
  rw [neg_zero] at hneg
  rw [← hneg, ← intervalIntegral.integral_add (show IntervalIntegrable (fun y ↦ f (-y)) volume 0 Y from (hf.comp continuous_neg).intervalIntegrable ..)
    (hf.intervalIntegrable ..)]
  congr 1
  apply intervalIntegral.integral_congr
  intro y _
  exact (add_comm ..).trans (cut_pair z ν y)

private theorem cos_bound (w : ℂ) : ‖cos w‖ ≤ Real.exp |w.im| := by
  rw [Complex.cos, norm_div]
  norm_num
  have h := norm_add_le (exp (w*I)) (exp (-w*I))
  simp [Complex.norm_exp] at h
  linarith [Real.exp_le_exp.mpr (le_abs_self w.im),
    Real.exp_le_exp.mpr (neg_le_abs w.im)]

private theorem strip_bound (z ν x y : ℝ) :
    ‖stripKernel z ν (x+y*I)‖ ≤ Real.exp (-z*Real.sin x*Real.cosh y + |ν| * |y|) := by
  have h := cos_bound ((ν : ℂ)*(x+y*I))
  simp [abs_mul] at h
  unfold stripKernel
  rw [norm_mul,Complex.norm_exp,Real.exp_add]
  have hr : (-(z : ℂ)*sin (x+y*I)).re = -z*Real.sin x*Real.cosh y := by
    rw [sin_add,sin_mul_I,cos_mul_I,← ofReal_sin,← ofReal_cos,← ofReal_sinh,← ofReal_cosh]
    simp [Complex.mul_re, -ofReal_sin]; ring
  rw [hr]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- A uniform integrable exponential bound for the entire lifted integrand. -/
private theorem damping {c : ℝ} (hc : 0 < c) (b : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    -c*Real.cosh v + b*v ≤ (b+1)^2/c-v := by
  have hq : v^2/4 ≤ Real.cosh v := by
    rw [Real.cosh_eq]
    linarith [Real.quadratic_le_exp_of_nonneg hv, Real.exp_pos (-v)]
  have hs := sq_nonneg (c*v-2*(b+1))
  have hp := mul_le_mul_of_nonneg_left hq hc.le
  apply (le_sub_iff_add_le).mpr
  apply (le_div_iff₀ hc).mpr
  nlinarith [mul_le_mul_of_nonneg_right hp hc.le]

private theorem connector_estimate {z a lo b : ℝ} (hz : 0 < z) (ha : 0 < lo) (hla : lo ≤ a)
    (hab : a ≤ b) (hb : b ≤ Real.pi/2) (ν y : ℝ) :
    ‖connector z ν a b y‖ ≤
      (Real.exp ((|ν|+1)^2/(z*Real.sin lo)) * Real.exp (-|y|)) * |b-a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  rw [Set.uIoc_of_le hab] at hx
  have hsa := Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_pos] : lo < Real.pi)
  have hax := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
    (hx.2.trans hb) (hla.trans hx.1.le)
  apply (strip_bound z ν x y).trans
  rw [← Real.exp_add, Real.exp_le_exp]
  have hd := damping (mul_pos hz hsa) |ν| (abs_nonneg y)
  rw [Real.cosh_abs] at hd
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hax hz.le) (Real.cosh_pos y).le
  linarith

private theorem connector_vanish {z lo b : ℝ} (hz : 0 < z) (ha : 0 < lo)
    (hb : b ≤ Real.pi/2) (a : ℝ → ℝ) (hband : ∀ᶠ Y : ℝ in atTop, lo ≤ a Y ∧ a Y ≤ b)
    (ν : ℝ) (side : ℝ → ℝ) (hs : ∀ᶠ Y : ℝ in atTop, |side Y| = Y) :
    Tendsto (fun Y ↦ connector z ν (a Y) b (side Y)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun Y : ℝ ↦ (Real.exp ((|ν|+1)^2/(z*Real.sin lo)) * Real.exp (-Y)) * (b-lo))
  · filter_upwards [hs,hband] with Y h hy
    have he := connector_estimate hz ha hy.1 hy.2 hb ν (side Y)
    rw [h, abs_of_nonneg (sub_nonneg.mpr hy.2)] at he
    exact he.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hy.1 b) (by positivity))
  · simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
      (Real.exp ((|ν|+1)^2/(z*Real.sin lo)))).mul_const (b-lo)

/-- The full improper jump for contours lifting to Re θ = a. The integral
on the right is the defining integral of the modified Bessel K times the
Stokes multiplier. Here ν=1/3 gives the cube-series wave. -/
theorem strip_jump {z lo : ℝ} (hz : 0 < z) (ha : 0 < lo) (a : ℝ → ℝ)
    (hb : ∀ᶠ Y : ℝ in atTop, lo ≤ a Y ∧ a Y ≤ Real.pi/2) (ν : ℝ) :
    Tendsto (fun Y ↦ vertical z ν (a Y) (-Y) Y) atTop
      (𝓝 (I * ∫ y in Set.Ioi (0:ℝ),
        (↑(2 * Real.cos (ν*(Real.pi/2)) * Real.exp (-z*Real.cosh y) * Real.cosh (ν*y)) : ℂ))) := by
  let f := fun y : ℝ ↦ (↑(2 * Real.cos (ν*(Real.pi/2)) * Real.exp (-z*Real.cosh y) *
    Real.cosh (ν*y)) : ℂ)
  let C := Real.exp ((|ν|+1)^2/z)
  have hi : IntegrableOn f (Set.Ioi 0) := by
    have he := (integrableOn_exp_neg_Ioi 0).const_mul (2*C)
    have hf : Continuous f := by dsimp [f]; fun_prop
    apply he.mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
    have hpair := cut_pair z ν y
    change ‖f y‖ ≤ 2*C*Real.exp (-y)
    dsimp only [f]
    rw [← hpair]
    apply (norm_add_le ..).trans
    have h1 := strip_bound z ν (Real.pi/2) y
    have h2 := strip_bound z ν (Real.pi/2) (-y)
    have h3 := Real.exp_le_exp.mpr (damping hz |ν| (le_of_lt hy))
    simp only [Real.sin_pi_div_two, mul_one,Real.cosh_neg, abs_neg, abs_of_pos hy] at h1 h2
    rw [sub_eq_add_neg, Real.exp_add ((|ν|+1)^2/z)] at h3
    dsimp [C]
    linarith
  have hlim := (intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id).const_mul I
  have hup := connector_vanish hz ha le_rfl a hb ν id
    ((eventually_ge_atTop (0:ℝ)).mono fun Y h ↦ abs_of_nonneg h)
  have hdn := connector_vanish hz ha le_rfl a hb ν (fun Y ↦ -Y)
    ((eventually_ge_atTop (0:ℝ)).mono fun Y h ↦ (abs_neg Y).trans (abs_of_nonneg h))
  have ht := (hlim.add hdn).sub hup
  simp only [add_zero,sub_zero] at ht
  apply ht.congr'
  filter_upwards with Y
  rw [strip_rectangle z ν (a Y) (Real.pi/2) Y, vertical_cut]
  rfl

theorem cubic_uniformization (θ : ℂ) (h : cos θ ≠ 0) :
    4*(1-sin θ^2)*(cos (θ/3)/cos θ)^3 = 3*(cos (θ/3)/cos θ)+1 := by
  have ht := Complex.cos_three_mul (θ/3)
  rw [show 3*(θ/3) = θ by ring] at ht
  rw [show 1-sin θ^2 = cos θ^2 by linear_combination -(Complex.sin_sq_add_cos_sq θ)]
  field_simp [h]
  linear_combination -ht

/-- Horizontal coordinate of the upper/lower endpoints of a straight ray of
slope ±k in the original r-plane, at height ±y in its sine lift. -/
def rayAngle (k y : ℝ) := Real.arctan (Real.tanh y / k)

theorem ray_slope {k : ℝ} (hk : 0 < k) (y : ℝ) :
    let r := sin (↑(rayAngle k y) + y*I)
    r.im = k*r.re := by
  dsimp only
  rw [sin_add, sin_mul_I, cos_mul_I, ← ofReal_sinh, ← ofReal_cosh, ← ofReal_sin, ← ofReal_cos]
  simp [Complex.mul_re, Complex.mul_im, -ofReal_sin, -ofReal_cos, -ofReal_sinh]
  have ht := Real.tan_arctan (Real.tanh y/k)
  change Real.tan (rayAngle k y) = Real.tanh y/k at ht
  rw [Real.tan_eq_sin_div_cos,Real.tanh_eq_sinh_div_cosh] at ht
  have hc := (Real.cos_arctan_pos (Real.tanh y/k)).ne'
  change Real.cos (rayAngle k y) ≠ 0 at hc
  field_simp [hc,(Real.cosh_pos y).ne',hk.ne'] at ht
  linarith

private theorem rayAngle_band {k : ℝ} (hk : 0 < k) :
    ∀ᶠ Y : ℝ in atTop, Real.arctan ((1/3)/k) ≤ rayAngle k Y ∧ rayAngle k Y ≤ Real.pi/2 := by
  filter_upwards [eventually_ge_atTop (1:ℝ)] with Y hY
  refine ⟨Real.arctan_le_arctan_iff.mpr (div_le_div_of_nonneg_right ?_ hk.le),
    (Real.arctan_lt_pi_div_two _).le⟩
  rw [Real.tanh_eq, le_div_iff₀ (by positivity)]
  have hpos := Real.add_one_le_exp Y
  have hneg := Real.exp_le_one_iff.mpr (by linarith : -Y ≤ 0)
  linarith

private theorem primitive_path {G f : ℂ → ℂ} (hf : Continuous f)
    (hg : ∀ w, HasDerivAt G (f w) w)
    {γ γ' : ℝ → ℂ} (hγ : ∀ y, HasDerivAt γ (γ' y) y) (hc : Continuous γ') (l h : ℝ) :
    (∫ y in l..h, γ' y * f (γ y)) = G (γ h) - G (γ l) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := G ∘ γ)
  · intro y _
    exact (hg (γ y)).scomp y (hγ y)
  · exact (hc.mul (hf.comp
      (continuous_iff_continuousAt.mpr fun y ↦ (hγ y).continuousAt))).intervalIntegrable ..

def rayPath (k sign y : ℝ) : ℂ := ↑(rayAngle k y) + ↑y * (↑sign * I)

private theorem ray_smooth (k sign : ℝ) : ContDiff ℝ 1 (rayPath k sign) := by
  have ha : ContDiff ℝ 1 (rayAngle k) := by
    unfold rayAngle
    simp only [Real.tanh_eq_sinh_div_cosh]
    apply ContDiff.arctan
    exact (Real.contDiff_sinh.div Real.contDiff_cosh (fun y ↦ (Real.cosh_pos y).ne')).div_const k
  exact (Complex.ofRealCLM.contDiff.comp ha).add
    (Complex.ofRealCLM.contDiff.mul contDiff_const)

def rayIntegral (z ν k sign Y : ℝ) : ℂ :=
  ∫ y in 0..Y, deriv (rayPath k sign) y * stripKernel z ν (rayPath k sign y)

/-- Improper lateral jump on the two lifted paths from the origin. The preceding
slope identity identifies their sine images. No cancellation assumption or
asymptotic representation is an input. -/
theorem ray_jump {z k : ℝ} (hz : 0 < z) (hk : 0 < k) (ν : ℝ) :
    Tendsto (fun Y ↦ rayIntegral z ν k 1 Y - rayIntegral z ν k (-1) Y) atTop
      (𝓝 (I * ∫ y in Set.Ioi (0:ℝ),
        (↑(2 * Real.cos (ν*(Real.pi/2)) * Real.exp (-z*Real.cosh y) * Real.cosh (ν*y)) : ℂ))) := by
  obtain ⟨G,hG⟩ := (stripKernel_entire z ν).isExactOn_univ
  have hg w := hG w (Set.mem_univ w)
  apply (strip_jump hz (Real.arctan_pos.mpr (div_pos (by norm_num) hk)) _
    (rayAngle_band hk) ν).congr'
  filter_upwards with Y
  have hr (s : ℝ) := primitive_path (stripKernel_entire z ν).continuous hg (fun y ↦ ((ray_smooth k s).differentiable
    (by norm_num)).differentiableAt.hasDerivAt (x := y))
    ((ray_smooth k s).continuous_deriv (by norm_num)) 0 Y
  have hv := primitive_path (stripKernel_entire z ν).continuous hg (γ := fun t : ℝ ↦ ↑(rayAngle k Y) + ↑t*I) (γ' := fun _ ↦ I)
    (fun t ↦ by simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I |>.const_add (↑(rayAngle k Y) : ℂ))
    continuous_const (-Y) Y
  unfold vertical rayIntegral
  rw [← intervalIntegral.integral_const_mul, hv, hr 1, hr (-1)]
  simp [rayPath,rayAngle,sub_eq_add_neg]

/-- The cubic wave with the manuscript's sign and normalization. -/
theorem cubic_ray_wave {z k : ℝ} (hz : 0 < z) (hk : 0 < k) (n : ℕ) (hn : 0 < n) :
    Tendsto (fun Y ↦ (-(z : ℂ)/(2*↑Real.pi*I*n)) *
      (rayIntegral z (1/3) k 1 Y - rayIntegral z (1/3) k (-1) Y)) atTop
      (𝓝 ((-(↑(Real.sqrt 3) : ℂ)*z/(2*↑Real.pi*n)) *
        ∫ y in Set.Ioi (0:ℝ), (↑(Real.exp (-z*Real.cosh y)*Real.cosh (y/3)) : ℂ))) := by
  have h := (ray_jump hz hk (1/3)).const_mul (-(z : ℂ)/(2*↑Real.pi*I*n))
  have hcos : 2*Real.cos ((1/3)*(Real.pi/2)) = Real.sqrt 3 := by
    rw [show (1/3)*(Real.pi/2) = Real.pi/6 by ring, Real.cos_pi_div_six]; ring
  simp_rw [hcos,show ∀ y : ℝ, (1/3)*y = y/3 by intro y; ring, mul_assoc (Real.sqrt 3),
    Complex.ofReal_mul, integral_const_mul] at h
  simp only [Complex.ofReal_mul]
  convert h using 2
  field_simp [Complex.I_ne_zero, Real.pi_ne_zero, Nat.ne_of_gt hn]

/-- The original differential, integrated along r(y)=sin(θ(y)), with the
branch evaluated by continuation along the same lift. -/
def originalRay (z ν k sign Y : ℝ) : ℂ :=
  let θ := rayPath k sign
  ∫ y in 0..Y, deriv (fun t ↦ sin (θ t)) y *
    (exp (-(z : ℂ)*sin (θ y)) * (cos ((ν : ℂ)*θ y) / cos (θ y)))

theorem originalRay_eq (z ν k sign Y : ℝ) : originalRay z ν k sign Y = rayIntegral z ν k sign Y := by
  apply intervalIntegral.integral_congr
  intro y _
  let θ := rayPath k sign
  have hn : cos (θ y) ≠ 0 := by
    have hp : 0 < (cos (θ y)).re := by
      change 0 < (cos (↑(rayAngle k y) + ↑y * (↑sign * I))).re
      rw [← mul_assoc, ← Complex.ofReal_mul, cos_add, cos_mul_I, sin_mul_I,
        ← ofReal_cos, ← ofReal_sin, ← ofReal_sinh, ← ofReal_cosh]
      simp [Complex.mul_re, -ofReal_cos, -ofReal_sin, -ofReal_cosh, -ofReal_sinh]
      exact mul_pos (Real.cos_arctan_pos _) (Real.cosh_pos _)
    intro h
    simp [h] at hp
  have hd := (Complex.hasDerivAt_sin (θ y)).scomp y
    (((ray_smooth k sign).differentiable (by norm_num)).differentiableAt.hasDerivAt (x := y))
  change deriv (sin ∘ θ) y * _ = _
  rw [hd.deriv]
  change (deriv θ y * cos (θ y)) * _ = deriv θ y * stripKernel z ν (θ y)
  change (deriv θ y * cos (θ y)) *
    (exp (-(z : ℂ)*sin (θ y)) * (cos ((ν : ℂ)*θ y) / cos (θ y))) = _
  unfold stripKernel
  field_simp [hn]

/-- Negative-argument companion after r=sinh θ. -/
def hyperKernel (z ν : ℝ) (θ : ℂ) : ℂ := exp (-(z : ℂ)*sinh θ) * cosh ((ν : ℂ)*θ)

private theorem hyper_entire (z ν : ℝ) : Differentiable ℂ (hyperKernel z ν) := by
  unfold hyperKernel
  fun_prop

def hyperPath (k sign y : ℝ) : ℂ := ↑y + ↑(sign*Real.arctan (k*Real.tanh y))*I

private theorem hyper_smooth (k sign : ℝ) : ContDiff ℝ 1 (hyperPath k sign) := by
  have ha : ContDiff ℝ 1 (fun y ↦ sign*Real.arctan (k*Real.tanh y)) := by
    simp only [Real.tanh_eq_sinh_div_cosh]
    exact contDiff_const.mul ((contDiff_const.mul (Real.contDiff_sinh.div
      Real.contDiff_cosh (fun y ↦ (Real.cosh_pos y).ne'))).arctan)
  exact Complex.ofRealCLM.contDiff.add ((Complex.ofRealCLM.contDiff.comp ha).mul contDiff_const)

private theorem hyper_edge_bound {z k : ℝ} (hz : 0 < z) (ν : ℝ) {Y v : ℝ}
    (hY : 0 ≤ Y) (hv : |v| ≤ Real.arctan k) :
    ‖hyperKernel z ν (Y+v*I)‖ ≤ Real.exp (z*Real.cos (Real.arctan k) +
      (|ν|+1)^2/(z*Real.cos (Real.arctan k))) * Real.exp (-Y) := by
  let c := z*Real.cos (Real.arctan k)
  have hc : 0 < c := mul_pos hz (Real.cos_arctan_pos _)
  have hcos : Real.cos (Real.arctan k) ≤ Real.cos v := by
    simpa using Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg v)
      (le_trans (Real.arctan_lt_pi_div_two k).le (by linarith [Real.pi_pos])) hv
  have hw := cos_bound (((ν : ℂ)*(Y+v*I))*I)
  rw [cos_mul_I] at hw
  simp [abs_mul, abs_of_nonneg hY] at hw
  unfold hyperKernel
  rw [norm_mul,Complex.norm_exp]
  have hr : (-(z : ℂ)*sinh (Y+v*I)).re = -z*Real.sinh Y*Real.cos v := by
    rw [sinh_add, sinh_mul_I,cosh_mul_I, ← ofReal_sin, ← ofReal_cos, ← ofReal_sinh, ← ofReal_cosh]
    simp [Complex.mul_re, -ofReal_sinh, -ofReal_cos]; ring
  rw [hr]
  apply (mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le).trans
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have h1 := damping hc |ν| hY
  have h2 : Real.cosh Y - Real.sinh Y ≤ 1 := by
    rw [Real.cosh_eq,Real.sinh_eq]; linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hY)]
  have h3 := mul_le_mul_of_nonneg_left hcos (mul_nonneg hz.le (Real.sinh_nonneg_iff.mpr hY))
  have h4 := mul_le_mul_of_nonneg_left h2 hc.le
  dsimp [c] at *
  linarith

def hyperRay (z ν k sign Y : ℝ) : ℂ :=
  ∫ y in 0..Y, deriv (hyperPath k sign) y * hyperKernel z ν (hyperPath k sign y)

/-- The entire negative-argument companion has zero lateral jump. -/
theorem hyper_jump {z k : ℝ} (hz : 0 < z) (hk : 0 < k) (ν : ℝ) :
    Tendsto (fun Y ↦ hyperRay z ν k 1 Y - hyperRay z ν k (-1) Y) atTop (𝓝 0) := by
  obtain ⟨G,hG⟩ := (hyper_entire z ν).isExactOn_univ
  let g := hyperKernel z ν
  have hg w := hG w (Set.mem_univ w)
  let b := fun Y ↦ Real.arctan (k*Real.tanh Y)
  have edge (Y : ℝ) : hyperRay z ν k 1 Y - hyperRay z ν k (-1) Y =
      I*(∫ v in -(b Y)..b Y, g (Y+v*I)) := by
    have hr (s : ℝ) := primitive_path (hyper_entire z ν).continuous hg (fun y ↦ ((hyper_smooth k s).differentiable
      (by norm_num)).differentiableAt.hasDerivAt (x := y)) ((hyper_smooth k s).continuous_deriv (by norm_num)) 0 Y
    have hv := primitive_path (hyper_entire z ν).continuous hg (γ := fun v : ℝ ↦ ↑Y + ↑v*I) (γ' := fun _ ↦ I)
      (fun v ↦ by simpa using (Complex.ofRealCLM.hasDerivAt (x := v)).mul_const I |>.const_add (Y : ℂ))
      continuous_const (-(b Y)) (b Y)
    unfold hyperRay
    rw [← intervalIntegral.integral_const_mul,hv]
    change (∫ y in 0..Y, _ * g _) - (∫ y in 0..Y, _ * g _) = _
    rw [hr 1, hr (-1)]
    simp [hyperPath,b]
  let C := Real.exp (z*Real.cos (Real.arctan k)+(|ν|+1)^2/(z*Real.cos (Real.arctan k)))
  apply squeeze_zero_norm' (a := fun Y ↦ (C*Real.exp (-Y))*(2*Real.arctan k))
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with Y hY
    have h0 : 0 ≤ b Y := Real.arctan_nonneg.mpr (mul_nonneg hk.le (by
      rw [Real.tanh_eq_sinh_div_cosh]; positivity))
    have h1 : b Y ≤ Real.arctan k := Real.arctan_le_arctan_iff.mpr
      (by simpa using mul_le_mul_of_nonneg_left (Real.tanh_lt_one Y).le hk.le)
    rw [edge,norm_mul,norm_I,one_mul]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun v : ℝ ↦ g (Y+v*I))
      (a := -(b Y)) (b := b Y) (C := C*Real.exp (-Y)) (by
        intro v hv
        rw [Set.uIoc_of_le (by linarith)] at hv
        exact hyper_edge_bound hz ν hY ((abs_le.mpr ⟨hv.1.le,hv.2⟩).trans h1))
    rw [abs_of_nonneg (by linarith)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (by dsimp [C]; positivity))
  · simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C).mul_const (2*Real.arctan k)

theorem hyper_ray_slope (k y : ℝ) :
    let r := sinh (hyperPath k 1 y)
    r.im = k*r.re := by
  dsimp only [hyperPath]
  simp only [one_mul,sinh_add,sinh_mul_I,cosh_mul_I, ← ofReal_sinh, ← ofReal_cosh,
    ← ofReal_cos, ← ofReal_sin]
  simp [Complex.mul_re, Complex.mul_im, -ofReal_sin, -ofReal_cos, -ofReal_sinh, -ofReal_cosh]
  have h := Real.tan_arctan (k*Real.tanh y)
  rw [Real.tan_eq_sin_div_cos,Real.tanh_eq_sinh_div_cosh] at h
  field_simp [(Real.cos_arctan_pos _).ne', (Real.cosh_pos y).ne'] at h
  rw [Real.tanh_eq_sinh_div_cosh, ← mul_div_assoc]
  linarith

/-- The actual single Borel summand: positive-argument jump minus the
negative-argument companion, with both lifted from the origin. -/
theorem cubic_single_jump {z k : ℝ} (hz : 0 < z) (hk : 0 < k) (n : ℕ) (hn : 0 < n) :
    Tendsto (fun Y ↦ (-(z : ℂ)/(2*↑Real.pi*I*n)) *
      ((originalRay z (1/3) k 1 Y - originalRay z (1/3) k (-1) Y) -
       (hyperRay z (1/3) k 1 Y - hyperRay z (1/3) k (-1) Y))) atTop
      (𝓝 ((-(↑(Real.sqrt 3) : ℂ)*z/(2*↑Real.pi*n)) *
        ∫ y in Set.Ioi (0:ℝ), (↑(Real.exp (-z*Real.cosh y)*Real.cosh (y/3)) : ℂ))) := by
  have h0 := (hyper_jump hz hk (1/3)).const_mul (-(z : ℂ)/(2*↑Real.pi*I*n))
  simpa only [originalRay_eq,mul_sub _ (rayIntegral .. - rayIntegral ..),mul_zero,sub_zero]
    using (cubic_ray_wave hz hk n hn).sub h0

end
end CubicTheta
