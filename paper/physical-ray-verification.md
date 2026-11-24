# Coefficient separation at positive temperature

**Historical proof note.** Status statements below describe this stage of the argument. The [completed physical proof](marked-wave-proof.md) and the [Lean theorem](../PakStokes.lean) give the final result.

For the cube series, put \(x=t^{-1/2}\). The two Airy waves of mode \(n\) have the same decay rate on this ray. Their imaginary frequencies have opposite signs. This permits coefficient extraction on the ray where the original Poisson formula holds.

## From the cube sum to individual Fourier modes

For \(J_t(z)=\int_0^\infty e^{-t r^3+zr}\,dr\), take \(h=e^{-i\pi/6}\), \(k=\bar h\), and \(\alpha>0\) with \(\alpha^3=3t\). Lean applies Poisson summation to \(e^{-t|r|^3}\) by proving it is twice continuously differentiable and its first two derivatives are integrable. Splitting the Fourier integral at zero and changing scale on the two defining Airy rays gives
\[
 J_t(ib)=ikJ_t(-kb)+\frac{2\pi h}{\alpha}\operatorname{Ai}_{\rm contour}(bh/\alpha).
\]
The definition uses the lower ray inward and the upper ray outward. Subtracting \(i/b\) from the rotated background before estimating its real part gives
\[
 |\Re(ik J_t(-kb))|\le |ik|\,6t/(b\Re k)^4 .
\]
The proof uses \(1-e^{-tr^3}\le tr^3\). This makes the background summable. The real Airy corrections are then summable by subtraction from the summable Fourier series. The theorem for the original one-sided cube sum includes the zero frequency \(t^{-1/3}\Gamma(4/3)\) and the endpoint contribution \(1/2\). [Physical Fourier calculation](../PakStokes/PhysicalAiry.lean) · [Separate summability and series identity](../PakStokes/PhysicalBackground.lean) · [Airy contour, DLMF 9.5.4](https://dlmf.nist.gov/9.5.E4)

## Which beta kernel gives the wave

With \(T\sim\mathrm{Beta}(5/6,1/6)\), the required kernel is \(B(u)=\mathbb E(1+uT/2)^{-1/6}\). Its first coefficient is \(-5/72\). Keeping the last exponent and reversing the beta shapes gives \(-1/72\). Normalization at zero and an upper bound of one hold for both choices. The difference already changes the first inverse-action correction of a single wave. Equivalently one may reverse the shapes **and** change the last exponent to \(-5/6\), by symmetry of the two upper hypergeometric parameters. [Euler integral, DLMF 15.6.1](https://dlmf.nist.gov/15.6.E1)

For an independent mean-one exponential \(V\), the product \(VT\) has the gamma law with shape \(5/6\). Lean proves the underlying integral identity for arbitrary integrable test functions by positive convolution and a change of scale on each interval. Specializing it gives, for every \(\Re c>0\) and \(x>0\),
\[
 \int_0^\infty e^{-v}B(v/(cx))\,dv
 =\frac1{\Gamma(5/6)}\int_0^\infty e^{-y}y^{-1/6}
       (1+y/(2cx))^{-1/6}\,dy .
\]
The *same* kernel \(u\mapsto B(u/c)\) is analytic along the nonnegative ray, equals one at zero, and has norm at most one. The right side is the classical normalized Airy factor from DLMF 9.5.8, with \(cx=2X^{3/2}/3\). The fixed-ray comparison below proves that this is exactly the factor in the checked Poisson contour. [Beta–gamma transport](../PakStokes/BetaGammaTransport.lean) · [Analyticity and unit bound](../PakStokes/CubicEulerKernel.lean) · [Airy integral, DLMF 9.5.8](https://dlmf.nist.gov/9.5.E8)

## Differentiating and separating on the real ray

Write \(M_m(x)=\int_0^\infty e^{-xu}u^m F(u)\,du\). For a continuous kernel bounded by one, \(M'_m=-M_{m+1}\), and \(|M_m(x)|\le m!\) for \(x\ge1\). Differentiating \(e^{-cx}x^d M_m(x)\) gives three terms with factors \(-c,d,-1\). The last two change the indices to \((d-1,m)\) and \((d,m+1)\). Iteration gives a uniform budget with an \(x^2\) loss for the entire cubic family at each fixed derivative order \(j\). For \(c_n=a n^{3/2}\), \(\Re a>0\), its summable part is a constant times \(n^{2j} e^{-n\Re a}\). Leading-term limits for the moments show that the ratio of the \(j\)th ordinary derivative to the original wave tends to \((-c_n)^j\). The sign disappears for \(D_x=-d/dx\). These results apply directly to the correctly normalized Kummer integral, including the \(n^{-1/4}\) prefactor. [Real derivatives and estimates](../PakStokes/LaplaceWaveJets.lean) · [Cubic Kummer specialization](../PakStokes/CubicKummerJets.lean)

The algebra of absolutely summable expansions preserves exact sums under addition and multiplication. It pushes the same majorant through each grouping of equal complex rates. Order the distinct **real** decay rates. Once all lower rates vanish, the next cluster is smaller than every inverse power. Within that cluster, take the smallest power needed to obtain a nonzero limit from any active modal amplitude. The surviving leading coefficients would form a finite trigonometric polynomial tending to zero.

To isolate one frequency \(b\), remove each other frequency \(d\) in succession by replacing \(S(x)\) with \(S(x+\delta)-e^{id\delta}S(x)\), where \(\delta=\pi/(b-d)\). The target coefficient acquires a nonzero multiplier at every removal. The final single wave has constant modulus, proving that its coefficient was zero. This handles arbitrary finite collisions, including an exactly conjugate pair with infinitely many zeros of its real sum. For bounded-degree cubic products, positivity and \(n^{3/2}\to\infty\) imply there are finitely many tuples below each real-rate ceiling. Equality of both real and imaginary parts recovers the sums of the plus and minus indices separately. [Product and regrouping theorems](../PakStokes/WaveProducts.lean) · [Finite-frequency elimination](../PakStokes/PhysicalPhases.lean) · [Kernel-based separator](../PakStokes.lean)

## Matching the contour and Kummer integral

On \(X=hr\), \(r>0\), put \(z=2X^{3/2}/3\), using principal powers. A version of the Kummer expression for the *unscaled* Airy function is
\[
 G(X)=C e^{-z}T(z),\qquad T(z)=\int_0^\infty e^{-v}v^{-1/6}(v+2z)^{-1/6}\,dv,\qquad
 C=\frac{3^{-1/6}2^{-2/3}}{\sqrt\pi\,\Gamma(5/6)}.
\]
Let \(w\) denote the integrand. The integrand of \(3zT''+(1-6z)T'-T\) is exactly \(\partial_v[vw/(v+2z)]\). The primitive vanishes at both endpoints for \(\Re z>0\). Differentiation on compact subsets has an integrable majorant since \(|v+2z|\ge v+2\Re z\). This gives \(G''(X)=XG(X)\). On each physical ray \(\arg z=\pm\pi/4\), the real part of \((v+2z)^{-1/6}\) is positive, so \(T\) never vanishes. Both \(G\) and its first radial derivative decay exponentially.

The contour solution satisfies the same Airy ODE by integration by parts in its defining contour. It and its first radial derivative are bounded because \(\Re(h e^{\pm i\pi/3})\ge0\) and \(e^{-r^3/3}\) dominates both integrals. Thus the radial Wronskian is constant and tends to zero. The ratio of the two solutions is constant wherever \(r>0\). At the origin, dominated convergence gives \(G(0)=C\Gamma(2/3)\), and the contour gives \(3^{-1/6}\Gamma(1/3)/(2\pi)\). Gamma duplication makes these equal. This argument uses absolute estimates even on the contour leg with purely imaginary linear phase. Lean verifies the radial ODE, boundedness of the contour solution and its first derivative, its limit at zero, and the nonvanishing of that limit. The Kummer moments now discharge the comparison hypotheses. The formal proof normalizes the second solution by the contour value at zero divided by Γ(2/3). This avoids a gamma duplication step and retains an explicitly nonzero multiplier. Principal-power factorization and the physical change of scale then give the exact Kummer formula at every positive mode and temperature. [Kummer ODE and endpoint limits](../PakStokes/KummerEquation.lean) · [Contour identification and branch factors](../PakStokes/PhysicalKummer.lean) · [Physical contour ODE and comparison theorem](../PakStokes/AiryContourODE.lean) · [Wronskian criterion](../PakStokes/AiryWronskian.lean) · Independent numerical checks (numerical script omitted from this release)

## Scope of the certificate

Subtract the endpoint, gamma term, and rotated background from the original cube sum. For this explicitly defined residual, `cubeResidual_derivatives` identifies every ordinary derivative in inverse square-root temperature with its absolutely summable physical waves. Consequently each such derivative decays faster than every inverse power. The proof uses the strictly positive real decay of the lowest possible mode. [Physical scaling, derivatives and flatness](../PakStokes/PhysicalSeries.lean)

A polynomial in these derivatives with polynomially bounded coefficient functions has an exact product expansion. At each real-rate ceiling it contains only finitely many ungrouped tuples. Ordering the rates by the number of predecessors and grouping the distinct imaginary frequencies constructs the separator’s indexing. Integer padding permits empty clusters even for a polynomial consisting solely of a coefficient. Given an identity for this residual and two analytic Laplace representations in disjoint power classes at each full action, `separate_cube_residual_identity` proves every grouped coefficient vanishes. The theorem constructs the indexing, normal convergence estimates, product sums, and grouped zero total. [Polynomial evaluation](../PakStokes/PhysicalExpression.lean) · [Action enumeration](../PakStokes/PhysicalSpectrum.lean) · [Physical separator](../PakStokes.lean)

To finish Pak’s conjecture, the coefficient functions produced by the original equation still need the analytic representations used by this theorem. The individual background and wave jets now have checked analytic kernels. One must combine those representations under products with the transformed equation coefficients and under finite sums in a shared action fiber, then evaluate the selected mixed squarefree fibers as the top homogeneous coefficients of the transformed equation. Arbitrary polynomially bounded coefficients alone cannot suffice. The coefficient function could itself be an exponentially small wave. [Physical proof candidate](physical-action-proof.md)

## Straightening the background directly

Here is a real-axis route from the rotated background already in the Poisson theorem to a single ordinary Laplace kernel. It gives an explicit parametrization of the inverse contour used in the [physical Borel calculation](physical-airysum.md). For each frequency \(b=2\pi n\), set \(k=e^{i\pi/6}\), \(a=b\Re k\), and \(f_b(y)=y^3+kby\). The inverse branch \(y_b(v)\) for \(v\ge0\) lies in \(-\pi/6\le\arg y\le0\). It admits the following elementary real parametrization, with \(u\ge0\):
\[
 t=\frac1{\sqrt3(1+u^2)},\qquad s=u\sqrt{\frac{a}{3-t^2}},\qquad y=s(1-it).
\]
Substitution gives \(\Im f_b(y)=0\) and \(\Re f_b(y)\ge as\ge au\sqrt{a/3}\). The continuous curve starts at zero and covers every nonnegative value of \(v\). For two points in the closed sector, all three quadratic products in \((f_b(y)-f_b(z))/(y-z)=y^2+yz+z^2+kb\) have nonnegative real part. Consequently \(|f_b(y)-f_b(z)|\ge a|y-z|\), the inverse is unique there, and \(\Re f_b'(y)\ge a\). The analytic inverse function theorem supplies a holomorphic branch near every point of the positive ray, including zero.

For \(p=t_{\rm temp}^{-1/2}>0\), scale the integration variable in the rotated Fourier mode by \(p\). Its exponent is then \(-pf_b(y)\). Deform the real axis to the displayed curve by a vertical connector at real coordinate \(s\). Throughout that connector \(\Re y^3\ge0\) and \(\Re(kby)\ge as\). Its contribution is bounded by \((s/\sqrt3)e^{-pas}\). The integrand is entire and the connector vanishes at infinity. Changing coordinate to \(v=f_b(y)\) gives the mode as \(p\int_0^\infty e^{-pv}K_b(v)\,dv\), where
\[
 K_b(v)=2\Re\!\left(\frac{ik}{3y_b(v)^2+kb}-\frac{i}{b}\right),\qquad
 |K_b(v)|\le \frac{6v^2}{(\Re k)^3 b^4}.
\]
Indeed the complex difference is \(-3iy_b(v)^2/[b(3y_b(v)^2+kb)]\), and \(|y_b(v)|\le v/a\). Subtraction leaves the real part unchanged. The \(b^{-4}\) bound justifies summing all modes under the Laplace integral and differentiating in \(p\) at any fixed order on compact positive intervals. For complex analyticity of the sum near any fixed real \(v\), scaling gives \(y_b(v)=\sqrt b\,y_1(v/b^{3/2})\). The analytic germ at zero and its quadratic cancellation bound the tail uniformly on a complex neighborhood. The paired real part extends by adding the reflected conjugate germ.

Lean proves the inverse geometry, analyticity of each subtracted kernel, the finite connector estimate, the exact deformation of the improper integral, and the normalized Laplace identity for the full background summed over all Fourier modes. The real-axis bound for its summed kernel is also checked. The complex tail converges normally on a disk about each real point after finitely many modes have been removed. Lean uses that argument to prove real analyticity of the full kernel on the ray, including the origin. [Contour deformation and summed identity](../PakStokes/BackgroundContour.lean)

Independent quadrature compares the original rotated integral with the inverse kernel itself and its first two temperature-coordinate derivatives at three values of \(p\) and two Fourier modes. [Inverse branch](../PakStokes/BackgroundInverse.lean) · Independent quadratures (numerical script omitted from this release)

Write \(K=\sum_b K_b\), and let \(M_j(p)=\int_0^\infty e^{-pv}(-v)^j K(v)\,dv\). Then \(B(p)=pM_0(p)\), and for each \(j\ge1\),
\[
 B^{(j)}(p)=pM_j(p)+jM_{j-1}(p).
\]
Here \(B\) denotes the rotated background in the coordinate \(p\). Each moment kernel is analytic on the ray and exponentially bounded. Lean proves the identity as a germ for every derivative order and verifies the exact predicate required of kernels by the separator. The theorem for the regularized cube series inserts these derivatives as zero-action terms. Its input subtracts only the explicit endpoint and gamma term from the original series. Lean now constructs the grouped two-parity representations and proves the nonlinear conclusion using a Jacobian in the squarefree marks. [Physical theorem, transfer and controls](marked-wave-proof.md). [Analyticity of the summed kernel](../PakStokes/BackgroundAnalytic.lean) · [Differentiated background](../PakStokes/BackgroundJets.lean) · [Polynomial substitution](../PakStokes/RegularCube.lean) · [Regularized cube separator](../PakStokes.lean)

Four physical samples also recover the first complex action with a fixed-step recurrence and a phase-independent leading determinant. [Derivation and measured accuracy](four-temperature-action.md)
