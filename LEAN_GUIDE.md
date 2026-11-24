# Checking the cubic theta argument in Lean

The target is Pak’s Conjecture 2.6. It asserts that the series $H(q)=\sum_{m\ge0}q^{m^3}$ satisfies no nonzero algebraic differential equation over $\mathbb C(q)$. The root theorem `CubicTheta.pak_conjecture_2_6` proves algebraic independence of $q,H,H',H'',\ldots$ over $\mathbb C$ inside $\mathbb C[[q]]$. It has no hypotheses. The independent variable is included so polynomial coefficients in $q$ are covered directly. [Physical proof and transfer lemma](paper/marked-wave-proof.md) · [Pak, p. 9](https://www.math.ucla.edu/~pak/papers/ICM-paper9.pdf)

## What Lean checks

| Theorem | Role |
|---|---|
| [pak_conjecture_2_6](PakStokes.lean) and [pak_formal_transfer](PakStokes/PakTransfer.lean) | Proves the conjecture for the formal series. Any putative relation gives a local finite polynomial differential system and hence an autonomous equation on the regularized physical sum. |
| [regular_cube_no_autonomous_ade](PakStokes.lean) | A polynomial in the actual physical jets vanishing on a tail is the zero polynomial, at every order and degree. |
| [group_parities](PakStokes/PhysicalParity.lean) and [independent_marked_jets](PakStokes/PhysicalJacobian.lean) | Each action coefficient has a checked two-parity representation. Its squarefree labels turn product regrouping into power-series multiplication, with a unit Jacobian on the marked jets. |
| [cubeSeries_airy_split](PakStokes/PhysicalBackground.lean) | From the positive-temperature cube series, proves the exact gamma term and separately summable rotated-background and Airy-contour corrections. |
| [cubicBeta_raySum](PakStokes/BetaGammaTransport.lean) and [cubicBeta_analytic](PakStokes/CubicEulerKernel.lean) | Identifies the normalized Euler kernel with the Kummer integral after Laplace summation. The same kernel is analytic and uniformly bounded by one along the physical ray. |
| [kummerSum_derivatives and kummer_mode_jet_ratio](PakStokes/CubicKummerJets.lean) | For every order, differentiates the exact Kummer series with cubic rates and obtains its termwise budget and individual jet limits. |
| [background_eq_raySum](PakStokes/BackgroundContour.lean) | Identifies the full rotated physical background with a single ordinary Laplace sum. Its individual inverse-cubic kernels are analytic, with a summable bound proportional to the inverse fourth power of the Fourier frequency. |
| [physical_contour_factor](PakStokes/PhysicalKummer.lean) | Identifies the contour from Poisson summation with the normalized Kummer factor on the physical ray, including its nonzero constant and principal branches. |
| [cubeResidual_derivatives and cubeResidual_flat](PakStokes/PhysicalSeries.lean) | Starting with the original cube sum minus its rotated background and polar terms, identifies every derivative with its absolutely convergent wave expansion and proves flatness to every algebraic order. |
| [background_derivatives](PakStokes/BackgroundJets.lean) | Every derivative of the actual background is a linear combination of two moments. The summed kernel and its polynomial moments satisfy the analytic and exponential growth hypotheses on the real ray. |
| [separate_regular_cube_identity](PakStokes.lean) | Inserts the background jets at zero action, then applies the separator to a polynomial in derivatives of the original cube sum with only its explicit endpoint and gamma term subtracted. The grouped analytic representations are inputs. |
| [separate_cube_residual_identity](PakStokes.lean) | Expands an actual polynomial identity in these derivatives, enumerates its full actions and proves separate vanishing assuming analytic two-parity representations of the grouped coefficients. |
| [separate_physical_ray_sums](PakStokes.lean) | Takes an ungrouped absolutely convergent expansion, a real-rate enumeration with finite frequency clusters, and the two-parity kernel representations. It proves that each full complex-action coefficient vanishes. |
| [raySum_leading and raySum_dichotomy](Laplace.lean) | For $L(F)(x)=\int_0^\infty e^{-u}F(u/x)\,du$, an analytic kernel on the ray with exponential growth is either zero along the ray or has a first term. If $F(v)=v^n g(v)$ near zero, then $x^n L(F)(x)\to n!g(0)$. The proof uses the analytic identity theorem, dominated convergence, and the Gamma integral. |
| [raySum_product](LaplaceProduct.lean) and [borelProduct_analytic](KernelAnalytic.lean) | The ordinary convolution $F*G$ gives $L(F)L(G)=xL(F*G)$ on the common convergence half-line. The convolution preserves exponential growth there and holomorphy on a shared open domain stable under contraction toward the origin. The factor $x$ matters with this normalization. |
| [rawLaplace_deriv](LaplaceDerivative.lean) | In the unnormalized Laplace integral, differentiation replaces $F(v)$ by $-vF(v)$. The integrable bound is proved uniformly in a neighborhood of the differentiation point. Together with the product rule this also handles normalized sums. |
| [separate_actions](ActionSeparation.lean) and [separate_ray_sums](PakStokes.lean) | After actions are grouped and ordered, a zero sum forces each coefficient to vanish as a germ. The specialized theorem derives detectability from representations by analytic kernels in two distinct power classes, including integer and half-integer powers. An arbitrary oscillatory factor of unit norm is allowed at each action. |
| [normalized_branches_interchange](CubicLateral.lean) | For the branches normalized to 1 of $(4-27z)K^3=3K+1$ on opposite nonreal rays, termwise lateral integration is justified. The cubic equation bounds each branch along the full ray and gives $K(z)-1=O(|z|)$ near zero. The factors $1/n$ and the argument $u^2/n^3$ then give an integrable majorant proportional to $e^{-u}u^2/n^4$. The Lean statement takes the normalized continuous branches on the rays as inputs. |
| [cut_root and cut_root_difference](CubicLateral.lean) | Write $27z/4=1+S^2$, where $S=\sinh(3t)$, $s=\sinh t$ and $h=\cosh t$. The two values $(s\pm i\sqrt3\,h)/(2S)$ solve the cubic on the cut and their difference is $i\sqrt3\,h/S$. Lean verifies the algebra from the hyperbolic identities. Identifying the upper and lower continuations with these roots requires branch information. |
| [ray_jump, hyper_jump and cubic_single_jump](CutContour.lean) | In the sine coordinate, the difference of the two improper ray integrals equals the defining real Bessel integral for every real order. The negative-argument companion has zero jump. The cubic specialization includes its sign, the factor $1/n$ and its temperature normalization. |
| [jumpKernel_bound and jump_moment_limit](CubicJump.lean) | For the actual cubic cut kernel $G(v)=\cosh(\operatorname{arcosh}(1+v)/3)/\sqrt{2+v}$, Lean proves $0<G(v)\le1/\sqrt2$ for $v\ge0$. For every $h>0$, the rescaled integral with weight $e^{-u}u^{h-1}$ tends to $\Gamma(h)/\sqrt2$. This includes every half-integer moment needed for the wave derivatives. |
| [transfer_both_on_ray](BorelTransfer.lean) and [complexLaplace_derivative](DirectionalLaplace.lean) | Given common analytic continuation, ray growth and all-orders flatness on the physical ray, a differential polynomial in the corresponding Laplace sums vanishes exactly on both sides at the same complex frequencies. The kernel proof covers sums, products and ordinary complex derivatives of arbitrary finite order. |
| [squarefree_action_separation and nonsquarefree_action_repeats](CubicActions.lean) | For $A_n=n\sqrt n$, the squarefree targets are independent of the rational span of all smaller positive actions. Every positive nonsquarefree target is an integer multiple of a single smaller action. |
| [mixed_jet_grid and mixed_subset_diagonal](MixedActions.lean) | The jet vectors form a Vandermonde basis in each slot. The complement polynomial for one subset of distinct nodes vanishes on all other equal-sized samples. These are the algebraic checks for the [physical-wave proof candidate](paper/physical-action-proof.md). |
| [characteristic_zero](PakStokes.lean) | Given infinitely many distinct actions with the stated normalized linearized jet identities and limits, their common characteristic polynomial vanishes. The sum can include indices whose limiting coefficients are zero. |
| [no_eventual_linear_ode](CubeLinear.lean) | For every finite sum $\sum_{j=0}^r q^j P_j(q\,d/dq)H(q)$, eventual vanishing of its coefficients implies every $P_j=0$. Lean proves this directly using the cube-indicator coefficient formula. Growing gaps isolate each shift on infinitely many cubes. This is the classical linear obstruction. The usual conversion of rational-coefficient linear ODEs to Euler-operator form by clearing denominators is elementary and outside the Lean statement. |

The tail estimate allows $\lvert A_i(x)\rvert\le b_i e^{Rw_i} x^K$ with $\sum b_i<\infty$. The fixed reserve $R$ lets one summably dominate polynomial growth in the action index. For each fixed $n$, the bound after removing $e^{-w_n x}$ decays at least as $x^K e^{-(w_{n+1}-w_n)x}$ times a constant depending on $n$. No global minimum spacing is required. Individual coefficient germs can vanish beyond different thresholds.

The analytic-kernel condition is essential. With two actions 1 and 2 and coefficients $A_1(x)=e^{-x}$ and $A_2(x)=-1$, the total $e^{-x}A_1+e^{-2x}A_2$ vanishes identically. The first coefficient is nonzero even though its power expansion vanishes to every order. This explains why simply comparing formal power series would be insufficient.

## The single-cut integral

Write $r=u/\omega$, $z=\omega/s>0$ and $K_\nu(r)=\cos(\nu\arcsin r)/\sqrt{1-r^2}$, normalized at zero. For the cubic kernel take $\nu=1/3$. Set $r=\sin\theta$ and continue from $\theta=0$. The differential becomes the entire function $e^{-z\sin\theta}\cos(\nu\theta)\,d\theta$. The triple-angle identity gives $4(1-r^2)K_{1/3}^3=3K_{1/3}+1$. Its root at $r=0$, $K=1$ is simple, so this parametrization continues the germ used in the paper.

For the straight rays $\operatorname{Im}r=\pm k\operatorname{Re}r$, $k>0$, set $a(y)=\arctan(\tanh(y)/k)$. Their lifts are $\theta_\pm(y)=a(y)\pm iy$, $y\ge0$. Indeed $\operatorname{Re}r=\sin(a(y))\cosh y$ increases from zero to infinity and $\operatorname{Im}r=\pm\cos(a(y))\sinh y$. The lift stays away from zeros of $\cos\theta$. Both paths start at zero, so an entire primitive expresses their finite difference as a single vertical integral from $a(Y)-iY$ to $a(Y)+iY$. Move it to $\operatorname{Re}\theta=\pi/2$ by a rectangle. On the two horizontal connectors the absolute integrand is bounded by $\exp(-z\sin(x)\cosh Y+|\nu|Y)$, uniformly tending to zero since $a(Y)$ stays bounded away from zero for large $Y$. The same estimate times the bounded path speed proves absolute convergence on the two lifted rays individually.

On the cut $\sin(\pi/2\pm iy)=\cosh y$. Combining orientations gives the exact identity
\[
 \int_{\mathrm{upper}} e^{-zr}K_\nu(r)\,dr-
 \int_{\mathrm{lower}} e^{-zr}K_\nu(r)\,dr
 =2i\cos(\pi\nu/2)\int_0^\infty e^{-z\cosh y}\cosh(\nu y)\,dy
 =2i\cos(\pi\nu/2)K_\nu^{\rm Bessel}(z).
\]
The multiplier vanishes for odd integer orders; for instance $K_1(r)=1$ and $K_3(r)=1-4r^2$. This family checks the orientation and gives exact controls for jump detection. [Lean contour calculation](CutContour.lean) · [Classical Bessel integral](https://dlmf.nist.gov/10.32.E9)

For the other term in the Borel germ, $K_{1/3}(ir)=\cosh(\operatorname{arsinh}(r)/3)/\sqrt{1+r^2}$ is analytic in the right half-plane and at the origin. On every closed sector $|\arg r|\le\delta<\pi/2$ it is $O_\delta(|r|^{-2/3})$ at infinity, by the logarithmic formula for $\operatorname{arsinh}$. Equivalently set $r=\sinh\theta$. The differential becomes $e^{-z\sinh\theta}\cosh(\nu\theta)\,d\theta$, entire in $\theta$. The two ray lifts $\theta=y\pm i\arctan(k\tanh y)$ have endpoints on a vertical segment of bounded length; on it $\Re\sinh\theta\ge\sinh y\cos(\arctan k)$. Lean proves that this segment contributes zero in the limit. This proves equality of the two companion integrals. The manuscript's prefactor therefore gives
\[
 W_n=-\frac{\sqrt{3}}{2\pi n}z_n K_{1/3}^{\rm Bessel}(z_n),\qquad z_n=\omega_n/s.
\]
The cut series converges absolutely. In fact $K_{1/3}^{\rm Bessel}(z)\le K_{1/2}^{\rm Bessel}(z)=\sqrt{\pi/(2z)}e^{-z}$ by monotonicity of $\cosh(\nu y)$ in $\nu\ge0$. Writing $z_n=A n^{3/2}$ bounds the tail starting at $n=L\ge1$ by
\[
 \frac{\sqrt{3A}}{2\sqrt{2\pi}}\,
 \frac{L^{-1/4}\exp(-A L^{3/2})}{1-\exp(-3A\sqrt{L}/2)} .
\]
This follows by convexity of $n^{3/2}$. The Lean theorem uses the integrals parametrized by their explicit lifts and the defining real Bessel integral. Identifying the normalized analytic germ with the manuscript’s binomial series, equating these parameters to its conventional straight-ray parameter, and assembling the infinite series with the displayed tail estimate are on-paper steps. It does not require numerical branch choices. Original-ray quadrature including odd-order controls (numerical script omitted from this release)

## The earlier lateral-summation argument

The formal proof above uses the physical ray and squarefree marking. The earlier lateral argument has separate continuation hypotheses. [Physical proof, transfer lemma and controls](paper/marked-wave-proof.md)

A simplification for the wave amplitudes is available on paper. With $z=\omega/s$ normalize the Bessel amplitude to $A(z)=\sqrt{2z/\pi}\,e^zK_{1/3}(z)$. Its ordinary Borel kernel is
\[
 B(u)={}_2F_1(1/6,5/6;1;-u/2)
     =\mathbb E[(1+uT/2)^{-1/6}],\qquad T\sim\mathrm{Beta}(5/6,1/6).
\]
Thus $B$ is holomorphic on $\mathbb C\setminus(-\infty,-2]$ and $|B(u)|\le1$ throughout the right half-plane. Rescaling by any positive $\omega$ preserves that common half-plane. For real $z>0$, if $V$ is an independent exponential of mean one, then $VT$ is Gamma with shape $5/6$ and unit rate. This follows by changing variables from two independent Gamma variables of shapes $5/6$ and $1/6$ to their sum and ratio. Substitution into Kummer’s integral gives $A(z)=\int_0^\infty e^{-v}B(v/z)\,dv$, and analytic continuation gives the right half-plane identity. Direct quadrature and the Bessel evaluation agreed within $1.1\times10^{-55}$ at $z=1/2,3,2+i/2$ with 55 decimal digits of arithmetic. This calculation makes the common direction for the wave factors explicit. The separate lateral background still requires its own kernel and contour estimates. [Kummer integral](https://dlmf.nist.gov/13.4.E4) · [Bessel identity](https://dlmf.nist.gov/13.6.E10)

## Reproduce

Use the repository root so its pinned toolchain and mathlib revision apply. The first build requires a network connection for dependencies and their compiled cache.

```sh
# Run from the repository root.
lake exe cache get
lake build +PakStokes
for mod in ActionSeparation CubeLinear CubicJump CubicLateral CutContour Laplace LaplaceProduct KernelAnalytic LaplaceDerivative DirectionalLaplace BorelTransfer CubicActions MixedActions \
  PakStokes.PhysicalAiry PakStokes.PhysicalBackground PakStokes.WaveProducts PakStokes.PhysicalPhases \
  PakStokes.BetaGammaTransport PakStokes.CubicEulerKernel PakStokes.LaplaceWaveJets \
  PakStokes.CubicKummerJets PakStokes.AiryWronskian PakStokes.AiryContourODE \
  PakStokes.KummerEquation PakStokes.PhysicalKummer PakStokes.PhysicalSeries \
  PakStokes.PhysicalExpression PakStokes.PhysicalSpectrum PakStokes.BackgroundInverse PakStokes.BackgroundContour \
  PakStokes.BackgroundAnalytic PakStokes.BackgroundJets PakStokes.RegularCube \
  PakStokes.RealRayExtension PakStokes.RayAlgebra PakStokes.PhysicalParity PakStokes.ActionCoordinates \
  PakStokes.MarkedSeries PakStokes.MarkedJacobian PakStokes.PhysicalJacobian PakStokes.ThetaControls \
  PakStokes.CubeNome PakStokes.OrdinaryPoint PakStokes.PolynomialFlow PakStokes.NomeChart PakStokes.PakTransfer; do
  lake env leanchecker "$mod" || exit 1
done
printf '%s\n' 'import LeanChecker' '#eval replayFromImports `PakStokes' | lake env lean --stdin
printf '%s\n' 'import PakStokes' '#print axioms CubicTheta.pak_conjecture_2_6' | lake env lean --stdin
```

Each leaf is replayed against its compiled imports. The last two commands replay the exact root module and report the axioms used by the conjecture theorem. The expected list is `propext`, `Classical.choice` and `Quot.sound`. Passing a namespace prefix to `leanchecker` can select several modules for parallel replay. The package uses Lean 4.36.0 and mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
