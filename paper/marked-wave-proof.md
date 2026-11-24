# Differential transcendence of the cubic theta series

Let $H(q)=\sum_{n\ge0}q^{n^3}$. The Lean theorem proves algebraic independence of $q,H,H',H'',\ldots$ over $\mathbb C$ inside the formal power series ring $\mathbb C[[q]]$. Every algebraic differential equation over $\mathbb C(q)$ would give a polynomial relation among these elements after clearing denominators. This gives exactly the differential transcendence in Pak’s Conjecture 2.6. [Pak, p. 9](https://www.math.ucla.edu/~pak/papers/ICM-paper9.pdf) · [Lean theorem](../PakStokes.lean)

## The physical theorem

Put $q(p)=e^{-1/p^2}$ for $p>0$ and
$$
 Y(p)=\sum_{n\ge0} e^{-n^3/p^2}-\tfrac12-\Gamma(4/3)p^{2/3}.
$$
For every $J\ge1$, if $P\in\mathbb C[X_0,\ldots,X_{J-1}]$ and $P(Y,Y',\ldots,Y^{(J-1)})=0$ on a tail of the positive ray, then $P=0$. There is no upper bound on the degree of $P$. The derivatives here are ordinary positive-sign derivatives in $p$. [Definition of the input](../PakStokes/RegularCube.lean) · [regular_cube_no_autonomous_ade](../PakStokes.lean)

**Proof.** Poisson summation and the Airy contour identity split each derivative into its zero-action background and two absolutely summable families of waves. Write their complex rates as $a n^{3/2}$ and $\bar a n^{3/2}$, with $\Re a=-\Im a>0$. Products add the rates. At bounded real decay only finitely many terms of each given polynomial occur, counting their multiplicities. The common exponential budget justifies regrouping the entire expansion. [Physical identity and estimates](physical-ray-verification.md) · [Finite windows](../PakStokes/PhysicalSpectrum.lean)

For $L(F)(p)=p\int_0^\infty e^{-pu}F(u)\,du$, direct convolution gives $L(F)L(G)=pL(F*G)$. Each kernel is analytic at every point of the closed positive ray and has exponential growth there. Holomorphic extensions on overlapping disks centered on the ray agree by the identity theorem. Shrinking their union to the points whose segment from zero stays inside gives an open domain on which convolution preserves analyticity. Convolving with the constant kernel $1$ raises the outside power of $p$ by one without changing the represented function, since $L(1)=1$. Thus finite sums of integer shifts can be aligned exactly within each parity. The differentiated wave moments occupy the half-integer class and the background moments the integer class. Their finite sums and products have a representative in each of these two classes. Watson’s lemma and the identity theorem detect the first nonzero power of each representative. The two parities have disjoint possible first powers. Together with real-frequency separation within each equal-decay cluster, this forces every full complex-action coefficient of the zero identity to vanish as a germ. This uses the checked convolution and differentiation formulas for these kernels. General directional summability provides wider context. [Closure](../PakStokes/RayAlgebra.lean) · [Application to the physical jets](../PakStokes/PhysicalParity.lean) · [Sauzin on 1-summability](https://arxiv.org/abs/1405.0356)

Write $n=d k^2$ with $d$ squarefree. Give the wave a formal variable $z_{d,+}$ or $z_{d,-}$ and encode it by $z_{d,\pm}^{k^3}$. Rational linear independence of the numbers $d\sqrt d$ recovers the integer coordinates within either sign. The real and imaginary parts of the rate recover the two signed totals separately. Consequently two products give equal complex rates exactly when their formal monomials agree. Use as coefficient ring $R$ the germs of complex-valued functions on the positive ray, identifying functions that agree eventually. Each coefficient is a finite sum in $R$. The product of marked series uses the ordinary finite sum over pairs of exponents adding to the target. Hence a physical identity gives an exact formal identity $P(F_0,\ldots,F_{J-1})=0$ in the marked jets $F_j$. Each coefficient can have its own threshold of vanishing. [Action coordinates](../PakStokes/ActionCoordinates.lean) · [Finite-fiber arithmetic](../PakStokes/MarkedSeries.lean)

Choose $J$ distinct prime indices $d_i$. The linear coefficient of $z_{d_i,+}$ in $F_j$ is precisely the fundamental wave amplitude of the $j$th derivative at $d_i$. After multiplication by $p^{-1/2}$, this row tends to
$$
 c_i(1,-a d_i^{3/2},\ldots,(-a d_i^{3/2})^{J-1}),\qquad c_i\ne0.
$$
The distinct nodes make the limiting determinant nonzero. The unscaled matrix is therefore invertible over $R$, using the pointwise reciprocal of its determinant on a tail. Its determinant is the constant coefficient of the determinant of the full formal Jacobian $(\partial_{z_{d_i,+}}F_j)$. A power series with unit constant coefficient is a unit, including over this germ ring. [Physical Vandermonde determinant](../PakStokes/PhysicalJacobian.lean)

Now differentiate the marked polynomial identity with respect to the $J$ marking variables. The invertible Jacobian forces every $(\partial_jP)(F_0,\ldots,F_{J-1})$ to vanish. If a nonzero relation existed, one of least total degree would have every partial derivative identically zero as a polynomial. In characteristic zero it would be a constant, and a nonzero complex constant survives in $R$. This proves the theorem. It needs just $J$ fundamental directions for $J$ jet coordinates, irrespective of the degree. The full formal identity contains coefficients at higher powers of the marks as well. [Jacobian criterion](../PakStokes/MarkedJacobian.lean)

## Transfer lemma for Pak’s formal series

**Lemma.** If $H(q)\in\mathbb C[[q]]$ satisfied any nonzero algebraic differential equation over $\mathbb C(q)$, then $Y(p)$ would satisfy a nonzero autonomous polynomial differential equation with complex constant coefficients on the positive ray.

**Proof.** Clear denominators. In Lean the coefficient of $q^k$ in $H$ is one if $k$ is a nonnegative cube and zero otherwise. The $j$th formal derivative has coefficients bounded in norm by $j!(k+1)^j$. On each smaller disk this justifies evaluation, termwise differentiation, and the Cauchy products appearing in the polynomial. The formal identity therefore holds analytically at every $q(p)=e^{-1/p^2}$, $p>0$. [Formal-to-analytic evaluation](../PakStokes/CubeNome.lean)

Write the coordinates as $v_0=q(p)$ and $v_{j+1}=H^{(j)}(q(p))$. Among nonzero polynomial identities in these coordinates choose one, $Q$, of least total degree. Let $v_n$ be its highest occurring variable. Its partial derivative $S=\partial_n Q$ is a nonzero polynomial of smaller degree, so $S(v(x))\ne0$ at some $x>0$. This step uses values on the actual solution. A relation in $v_0$ alone is impossible since $q'(x)=2q(x)/x^3\ne0$. [Ordinary-point selection](../PakStokes/OrdinaryPoint.lean)

On a neighborhood of $x$ take the finite state consisting of $v_0,\ldots,v_n$, $r=1/p$, $b=p^{2/3}$ and $w=1/S(v)$. Each state derivative is polynomial in the state. Indeed $q'=2r^3q$, $v_i'=q'v_{i+1}$ for $1\le i<n$, $r'=-r^2$ and $b'=2rb/3$. Differentiating $Q(v)=0$ determines the last derivative,
$$
 v_n'=-w\sum_{i<n}(\partial_i Q)(v)v_i'.
$$
The chain rule then gives $w'=-w^2(S(v))'$. The regularized sum $Y=v_1-1/2-\Gamma(4/3)b$ is a polynomial in the state, as is each successive derivative. If the state has $N$ coordinates, any $N+1$ such polynomials are algebraically dependent over $\mathbb C$ by the transcendence degree of a polynomial ring. This produces a nonzero autonomous relation on $Y$ near $x$. Its value is real analytic on the connected positive ray, so the relation holds everywhere there. The physical theorem rules it out. [Polynomial differential systems](../PakStokes/PolynomialFlow.lean) · [Change of variable and continuation](../PakStokes/NomeChart.lean) · [pak_formal_transfer](../PakStokes/PakTransfer.lean) · [pak_conjecture_2_6](../PakStokes.lean)

## Consequence for counting sums of cubes

Let $r_k(m)$ count ordered representations of $m$ as a sum of $k$ nonnegative cubes, for fixed $k\ge1$. Its generating function is $G_k=H^k$, so each $G_k$ is differentially transcendental over $\mathbb C(q)$. Indeed, if $G_k$ were differentially algebraic, its derivatives would generate a differential field of finite transcendence degree over $\mathbb C(q)$. Adjoining $H$, a root of $T^k-G_k$, gives an algebraic extension that is still a differential field in characteristic zero. It would contain all the derivatives of $H$, contradicting the theorem. This is an on-paper corollary about the entire counting series for each fixed $k$.

## Two controls

**A singular background.** Set $u=e^{-p/2}$, $y=u^2+u^3$, $z=y'$. The invertible linear coordinates $A=3y+2z$, $B=-2(y+z)$ equal $u^2,u^3$. Over $K=\mathbb C(p)$, $u$ is transcendental. In a purported polynomial relation in $u$, clear denominators, divide by the smallest power of $u$ present and let $p\to+\infty$. A nonzero polynomial in $p$ cannot be exponentially small. The ideal of first-order relations is generated by $P=A^3-B^2$. Division by $B^2-A^3$ leaves $r(A)+B s(A)$, whose two terms have disjoint even and odd powers of $u$. Also $y$ is transcendental over $K$, so the order one and the degree three in $z$ are minimal. Yet $P_z(y,y')=6u^4+4u^3>0$, while $P_z(0,0)=0$. Minimality on the solution cannot justify linearization on its zero background. [Checked arithmetic](../PakStokes/ThetaControls.lean)

**Jacobi’s square series.** Gaussian Poisson summation gives dual actions $\pi^2 n^2$ in $1/t$ at $q=e^{-t}$. Every $n\ge2$ has $n^2=(n-1)^2+(2n-1)$. Lagrange’s four-square theorem writes $2n-1$ as a sum of four squares, all with indices less than $n$. Omitting zeros gives an action collision using at most five smaller waves. For a test on an actual nonlinear identity, use the dual nome $Q=e^{-\pi^2/t}$ and normalize to $y=1+2\sum_{n\ge1}Q^{n^2}$. With $y_j=(Q\,d/dQ)^j y$, Jacobi’s equation is
$$
 (y^2 y_3-15 y y_1 y_2+30 y_1^3)^2+32(y y_2-3 y_1^2)^3
 -y^{10}(y y_2-3y_1^2)^2=0.
$$
Exact integer convolution through action 512 gives zero in every group. Removing the $n=2$ mode gives coefficient $-384$ at action 5, the first discrepancy. Full-action separation still works for squares. Independent squarefree marks fail because the same action can have different monomials. [Gaussian inversion and collisions in Lean](../PakStokes/ThetaControls.lean) · Executable check (numerical script omitted from this release) · [Ohyama, introduction](https://fe.math.kobe-u.ac.jp/FE/FE_pdf_with_bookmark/FE41-45-en_KML/fe44-377-389/fe44-377-389.pdf)
