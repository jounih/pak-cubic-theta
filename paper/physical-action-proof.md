# A direct proof candidate from the physical Airy correction

**Historical proof note.** Status statements below describe this stage of the argument. The [completed physical proof](marked-wave-proof.md) and the [Lean theorem](../PakStokes.lean) give the final result.

The exact Airy decomposition gives a second route to Pak’s Conjecture 2.6. It starts with an equation for the physical cube series and tests the *highest homogeneous degree* of that very equation. The test uses several distinct squarefree indices simultaneously. The analytic and arithmetic ingredients are set out below to permit independent review. The Lean package checks the physical Fourier decomposition, Kummer jets, and coefficient separation with finite oscillatory clusters. The concrete links still needed for a nonlinear theorem are recorded in the [physical-ray verification](physical-ray-verification.md).

## Two active rays

Use $p=t^{-1/2}$ and $D_p=-d/dp$. By the [physical identity](physical-airysum.md), the regularized series is $Y=B+\sum_{n,\pm}W_{n,\pm}$. The two waves for each $n$ are the analytic continuations of the two conjugate terms of the real Airy formula. Take the branch of every fractional power from $p>0$. The actions with respect to $p$ are
\[
 \lambda_{n,\pm}=\omega_1 n^{3/2} e^{\pm i\pi/4},\qquad
 \omega_1=\frac{2(2\pi)^{3/2}}{3\sqrt3}.
\]
In a small sector about $p>0$, the background is the continuation of its physical Borel sum and the Airy series converges normally. Thus the real identity extends by holomorphy. The sine integral itself was only used for real temperature.

Choose $p=e^{i\theta}x$, $x\to+\infty$, with $\tan\theta=1/(10\pi)$. The two positive projection factors $c_\pm=\cos(\theta\pm\pi/4)$ have transcendental ratio $(1-\tan\theta)/(1+\tan\theta)$. Any finite sum of the $n^{3/2}$ is real algebraic. Therefore equality of two projected rates $\omega_1(c_+ U+c_- V)$ forces $U$ and $V$ to agree separately. Positivity of both $c_\pm$ makes the projected rates locally finite for any bounded number of factors. Equal projected rates also carry the same complex exponential, including its phase.

## Analytic control for coefficient extraction

Up to a nonzero constant depending only on the sign, the exact normalized wave is
\[
 W_{n,\pm}(p)=p^{1/2} n^{-1/4}e^{-\lambda_{n,\pm}p} A(\lambda_{n,\pm}p),\quad
 A(z)=\sqrt{2z/\pi}\,e^z K_{1/3}(z).
\]
This follows from the Airy–Bessel identity with principal branches. On the tilted ray the normalized amplitude is an ordinary Laplace sum in $1/x$ with the analytic kernel
\[
 u\longmapsto {}_2F_1(1/6,5/6;1;-u/(2e^{i\theta}\lambda_{n,\pm})).
\]
The beta-integral representation bounds the unscaled kernel by one in the right half-plane. For both signs the scaled kernels are holomorphic and bounded on a wedge about the positive $u$-ray, and analytic at zero. The background also has a Laplace kernel there: rotate the physical Borel integration direction to $-\theta$ in the $\sigma=1/p$ coordinate. The rotation stays in the same cut-free wedge. This uses the kernel bounds in the [transfer note](equation-transfer.md) and Cauchy deformation with exponential damping at infinity. [Airy–Bessel identity](https://dlmf.nist.gov/9.6.E2) · [Beta kernel derivation](../LEAN_GUIDE.md)

After stripping its exponential, a fixed wave derivative belongs to $x^{1/2}$ times ordinary Laplace sums with convergent Laurent germs adjoined. This follows from $D_p=-e^{-i\theta}d/dx$, the product rule, and the Laplace derivative law. In particular $D_p^j W_{n,\pm}/W_{n,\pm}\to\lambda_{n,\pm}^j$ for fixed $n,j$. For uniform bounds, take Cauchy circles about $p=e^{i\theta}x$ of radius $\epsilon/(1+|\lambda_{n,\pm}|)$ with $\epsilon$ fixed and $x$ large. The normalized Bessel factor stays bounded in a closed proper subsector of its right half-plane, and the exponential on the circle changes in modulus by at most $e^\epsilon$. This yields
\[
 |D_p^j W_{n,\pm}|\le C_j x^{1/2}n^{-1/4}(1+|\lambda_{n,\pm}|)^j
 e^{-x\Re(e^{i\theta}\lambda_{n,\pm})}.
\]
The estimate justifies termwise differentiation and absolute products of bounded degree.

An equation for $H$ would give a nonzero polynomial $P(Y,D_pY,\ldots,D_p^JY)=0$ with convergent Laurent coefficients in $1/p$. The changes of jets at $q=e^{-1/p^2}$ and subtraction of the explicit pole give an invertible triangular substitution over convergent Puiseux germs. Taking the product over the finite ramification group gives a nonzero equation over ordinary convergent Laurent germs, valid on the physical branch because its original factor vanishes. Clear the poles. Let $D\ge1$ be the total degree in the jets.

Expand this exact equation using $Y=B+\sum W$. Group terms with the same projected rate, including the constant group. After removing the common phase, each grouped coefficient is a finite sum of powers $x^{k/2}$ times ordinary directional sums, allowing finitely many integer pole powers. Within each parity factor out the largest power; the remaining nonpositive integer powers are convergent germs in $1/x$. A directional sum either vanishes or has a first nonzero Taylor order; the two parities have distinct orders. Thus each nonzero grouped coefficient has a leading power in modulus. For the infinite tail take the product budget in the [regrouping estimate](equation-transfer.md), using $\min(c_+,c_-)>0$ and summing over both choices of sign. Each grouped coefficient must vanish as a germ by least-rate extraction. This is where a formal manipulation of exponentials alone would leave an analytic gap. [Kernel-checked separation statement](../PakStokes.lean)

## A mixed coefficient reads off the top degree

Choose $D$ *distinct* squarefree positive indices $d_1,\ldots,d_D$. Extract the action $\lambda_{d_1,+}+\cdots+\lambda_{d_D,+}$. Projection separates the signs, so only plus waves can contribute. Each $n=dk^2$ contributes $k^3$ in squarefree coordinate $d$. The target has exactly $D$ coordinates equal to one. The only representation consists of the $D$ selected waves, each once. Thus no lower-degree term, background factor or repeated wave contributes. [Squarefree independence in Lean](../CubicActions.lean)

Write $Q_p$ for the degree-$D$ homogeneous part of $P$ and $L_p$ for its symmetric $D$-linear polarization, normalized by $L_p(v,\ldots,v)=Q_p(v)$. Put $V_i=(D_p^jW_{d_i,+})_{0\le j\le J}$. The zero grouped coefficient gives $D!L_p(V_1,\ldots,V_D)=0$ after restoring the exponential. Choose the smallest vanishing order $r$ at $1/p=0$ among the nonzero coefficients of $Q_p$. Then $p^r Q_p$ tends coefficientwise to a nonzero homogeneous polynomial $Q$, with polarization $L$. Divide by the product of the $D$ waves, each eventually nonzero by the Airy asymptotic, and pass to the limit. For every distinct tuple we obtain
\[
  L(v(\lambda_{d_1,+}),\ldots,v(\lambda_{d_D,+}))=0,\qquad
  v(z)=(1,z,\ldots,z^J).
\]
The left side is a polynomial in $D$ independently varying complex arguments. Partition the infinite squarefree index set into $D$ disjoint infinite subsets and sample the $i$th argument from the $i$th subset. Repeated one-variable root counting shows the polynomial vanishes identically. The vectors $v(z)$ span $\mathbb C^{J+1}$ by the Vandermonde determinant, so multilinearity forces $L=0$ and hence $Q=0$, a contradiction.

Using distinct waves is essential to this particular top-degree test. For example $Q(y_0,y_1,y_2)=(y_0y_2-y_1^2)^2$ vanishes on *every* individual vector $v(z)$. On four distinct inputs the coefficient of $t_1t_2t_3t_4$ in $Q(\sum_i t_i v(z_i))$ is twice the sum of $(z_i-z_j)^2(z_k-z_l)^2$ over the three pairings. At $z_i=1,2,3,4$ it is $52$. This example exercises the obstruction that using one wave repeatedly would miss.

## An explicit finite test for a fixed order and degree

Only $J+D$ distinct squarefree plus waves are needed for the last algebraic step. Let $Z$ be their action values. For a $D$-element subset $S\subset Z$ write $g_S(z)=\prod_{a\in Z\setminus S}(z-a)$ and let $\ell_S$ be the linear form on jet vectors satisfying $\ell_S(v(z))=g_S(z)$. For a homogeneous polynomial $Q$ let $M_T(Q)$ be the coefficient of $\prod_{t\in T}u_t$ in $Q(\sum_{t\in T}u_t v(t))$. Then
\[
 M_T(\ell_S^D)=D!\prod_{t\in T}g_S(t).
\]
This vanishes whenever $T\ne S$ and is nonzero for $T=S$. The number of subsets is $\binom{J+D}{D}$, the dimension of the homogeneous polynomials of degree $D$ in $J+1$ variables. Thus the powers $\ell_S^D$ form a basis, and the exact reconstruction reads
\[
 Q(y)=\sum_{|S|=D}\frac{M_S(Q)\,\ell_S(y)^D}{D!\prod_{s\in S}g_S(s)}.
\]
These are asymptotic coefficients of exact wave products. The formula gives a finite obstruction once the common-direction extraction theorem applies. It supplies no finite-precision recovery guarantee. The subset interpolation itself is classical; the application here is to coefficients labeled by isolated cubic waves. The numerical companion uses exact rational arithmetic to reconstruct the example quartic from all fifteen four-wave samples on six nodes. Lean verifies the diagonal test and the separate multilinear Vandermonde-grid criterion. [Krick, Szanto and Valdettaro, §2](https://arxiv.org/abs/1503.00607) · Exact reconstruction (numerical script omitted from this release) · [Lean algebra](../MixedActions.lean)

The kernel-checked proof now uses squarefree marking variables and an invertible Jacobian to conclude the nonlinear contradiction on the physical ray. It uses the exact physical Airy identity and the checked two-parity closure above. [Completed physical proof and formal-series transfer lemma](marked-wave-proof.md)
