# The Airy correction on the physical temperature axis

For $t>0$ define $\alpha=(3t)^{1/3}$ and $h=e^{-i\pi/6}$. The cube series has the exact decomposition
\[
 \sum_{n\ge0} e^{-tn^3}=\tfrac12+\Gamma(4/3)t^{-1/3}+B(t)+E(t),
\]
\[
 B(t)=-2\int_0^\infty \frac{\sin(tu^3)}{e^{2\pi u}-1}\,du,\qquad
 E(t)=\frac{4\pi}{\alpha}\Re\!\left[h\sum_{m\ge1}
              \operatorname{Ai}\!\left(\frac{2\pi m h}{\alpha}\right)\right].
\]
Here $B(t)$ is the directional Borel sum of the regular formal series in the physical direction. The Airy series measures its precise difference from the regularized cube sum. This gives a direct route from the original series to the all-orders flatness needed in the [Lean transfer theorem](../BorelTransfer.lean). Lean now checks the Fourier-to-Airy contour calculation, the exact normalized Kummer representation, and the absolutely convergent expansion of every derivative of the residual in inverse square-root temperature. Lean also straightens the rotated background directly to an analytic inverse-cubic kernel at each mode and proves its summed Laplace identity. The sine-integral calculation below provides an alternative derivation. [Physical-ray verification](physical-ray-verification.md)

## Poisson summation and the Airy contour

Write $J(z)=\int_0^\infty e^{-t r^3+zr}\,dr$. Apply Poisson summation to $e^{-t|r|^3}$, whose second derivative is integrable and whose periodization converges uniformly. The zero frequency gives the displayed gamma term. Each positive frequency $b=2\pi m$ contributes $2\Re J(ib)$. The series of paired frequencies converges absolutely by two integrations by parts.

Set $L_b=\int_0^\infty e^{-br+it r^3}\,dr$. Rotating to $r=e^{i\pi/6}v$ gives $L_b=e^{i\pi/6}J(-b e^{i\pi/6})$. On the connecting arc of radius $R$ the exponential is bounded by $e^{-bR\cos(\pi/6)}$, since $\sin(3\arg r)\ge0$. Expanding $(e^{2\pi u}-1)^{-1}$ geometrically gives $B(t)=-2\sum_m\Im L_{2\pi m}$ with absolute interchange by $|\sin(tu^3)|\le tu^3$.

Let $\rho=e^{2\pi i/3}$. After subtracting the contribution $-2\Im L_b$, the remaining paired coefficient is
\[
 2\Re[J(ib)-\rho J(\rho ib)].
\]
The bracket is an integral from $\rho\infty$ to zero to $+\infty$ of $e^{-t z^3+ibz}\,dz$. Under $w=\alpha e^{-i\pi/3}z$ the exponent becomes $w^3/3-(bh/\alpha)w$. The transformed rays run from angle $+\pi/3$ to $-\pi/3$, reversing the usual Airy contour. The bracket equals $(2\pi h/\alpha)\operatorname{Ai}(bh/\alpha)$, including its phase. Summing gives $E(t)$. [Airy integral, DLMF 9.5.4](https://dlmf.nist.gov/9.5.E4)

## Identification with the cubic Borel kernel

Put $\sigma=\sqrt t$ and $p=1/\sigma$. In $L_b$ first scale $r=z/\sigma$, so the exponent is $-p(bz-i z^3)$. Deform the positive $z$-ray onto the curve on which $v=bz-i z^3$ is positive real. For $z=R e^{i\theta}$ the curve satisfies
\[
 0<\theta<\pi/6,\qquad R^2=b\sin\theta/\cos(3\theta).
\]
The right side increases from zero to infinity. Along the curve $v$ increases from zero to infinity since $b-3iz^2$ never vanishes in the wedge, the parametrization is regular, and $v$ is real and initially increasing. The connecting circular arcs again vanish by the linear damping $e^{-p b R\cos(\pi/6)}$.

The inverse is $z=(v/b)T(x)$ with $x=i v^2/b^3$ and $T=1+xT^3$, $T(0)=1$. Its derivative is $K(x)/b$, where $K=T+2xT'$ is precisely the algebraic germ in the manuscript. Thus
\[
 -2\Im L_b=-\frac{2p}{b}\int_0^\infty e^{-pv}\Im K(i v^2/b^3)\,dv.
\]
With $b=2\pi m$ this is the $m$th summand of the physical-direction Borel sum. The summed integral identity follows from the absolute bound on the paired sine modes and the cubic kernel tail estimate. The powers and signs in $B(t)$ can also be read by differentiation under the integral at $t=0$. Each derivative costs a power of $u^3$, which the denominator absorbs. For instance $B'(0)=-1/120$ and every even Taylor coefficient vanishes. This derivation of the physical expansion avoids comparing two analytic continuations of the zeta function. [Cubic kernel](main.tex) · [Three-ray bounds](equation-transfer.md)

## The defect changes sign infinitely often

Let $b=2\pi$ and $\chi=2b^{3/2}/(3\sqrt{6t})$. The leading asymptotic is
\[
 E(t)=2\sqrt\pi\,\alpha^{-3/4} b^{-1/4} e^{-\chi}
       \big[\cos(\chi-\pi/8)+O(\chi^{-1})\big],\qquad t\downarrow0 .
\]
Indeed $\tfrac23(bh/\alpha)^{3/2}=(1-i)\chi$. The standard Airy expansion on $\arg z=-\pi/6$ supplies the phase $-\pi/8$. For $m\ge2$ the corresponding absolute bound is proportional to $\alpha^{-3/4}m^{-1/4}e^{-m^{3/2}\chi}$, uniformly for sufficiently large $\chi$. Thus the first mode determines the sign along $\chi=k\pi+\pi/8$ for all sufficiently large integers $k$. Continuity gives infinitely many crossings of the regularized cube sum and its physical Borel sum, accumulating at $t=0$. Uniform Airy bounds in a small complex wedge, applied to both conjugate branches of the real-part formula, allow Cauchy estimates for each fixed derivative. The defect and all these derivatives are smaller than every power of $t$. [Airy asymptotics, DLMF 9.7.5](https://dlmf.nist.gov/9.7.E5)

A [second proof candidate for Pak’s conjecture](physical-action-proof.md) uses the Airy waves at distinct squarefree indices to extract the highest degree of an equation directly.

The physical value and its Borel sum therefore have the same expansion and the same formal jets. If a differential polynomial vanishes on the physical series after the variable and polar-term changes, substituting the physical Borel sum leaves an all-orders flat residual after clearing poles. This gives the source condition for the common-ray theorem. For a relation selected by minimizing degree among formal relations, its zero formal expansion yields the same condition directly.

The exponential scales and sectorial sums are part of the earlier analysis of lacunary series and generalized Euler–Jacobi sums. The result used here is the explicit positive-temperature decomposition with the Borel normalization of this manuscript. Costin and Huang give the cubic scales explicitly in equation (19) and use a first-quadrant contour in equation (60). A priority comparison of exact remainders requires matching those contours and sheets to the specified straight physical ray. Priority for this particular formula is unestablished. [Costin and Huang](https://arxiv.org/abs/0810.3027) · [Paris](https://arxiv.org/abs/1503.07329) · Direct numerical checks (numerical script omitted from this release)
