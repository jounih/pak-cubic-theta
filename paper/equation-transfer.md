# Transporting the cube-series equation across the Stokes cut

**Historical proof note.** Status statements below describe this stage of the argument. The [completed physical proof](marked-wave-proof.md) and the [Lean theorem](../PakStokes.lean) give the final result.

The two sums on opposite sides of the cut can have different values at the same temperature. The proof needs them to obey the same differential equation there. A way to check this is to transport the *residual* of the equation. The residual has one analytic Borel germ. If the residual vanishes to every power on the physical ray, the first nonzero Taylor coefficient of that germ would contradict Watson’s lemma. The zero germ then continues to both integration rays. This is a concrete instance of classical directional summation. [Lean theorem](../BorelTransfer.lean) · [Sauzin, Parts I–II](https://arxiv.org/abs/1405.0356)

## A common residual

Write a series as a pair $(c,F)$, where $c$ is its constant and $F$ is the derivative of its ordinary Borel transform. Thus $a_n\sigma^n$ contributes $a_n u^{n-1}/(n-1)!$ for $n\ge1$. In the inverse coordinate $p=1/\sigma$, evaluation on the Borel ray of direction $d$ is
\[
 T_d(c,F)(p)=c+\int_0^\infty e^{-p(d v)}\,d\,F(d v)\,dv .
\]
Here $d$ is fixed while $p$ varies. Integration by parts gives the manuscript’s normalized transform of $\widehat f$ when $c=\widehat f(0)$ and $F=\widehat f'$. The boundary at infinity vanishes sufficiently far inside the convergence half-plane.

Assume all input densities are holomorphic on a common connected open set containing zero and stable under contraction to zero. On each selected ray assume exponential growth. Under multiplication the pair becomes
\[
 (c,F)(b,G)=(cb,cG+bF+F*G),\qquad
 (F*G)(z)=z\int_0^1 F(tz)G((1-t)z)\,dt .
\]
The operator $-d/dp$ sends $(c,F)$ to $(0,uF)$. Iterating these rules gives a single residual pair $(a,R)$ for a finite differential polynomial, with the same domain of holomorphy. Absolute convergence justifies the product law. For differentiation a positive margin in $\Re(pd)$ absorbs each additional power of $v$. The code proves by induction that the value of the expression, interpreted with actual complex derivatives, equals $T_d(a,R)$ sufficiently far into each half-plane. [Complex Laplace laws](../DirectionalLaplace.lean) · [Residual representation](../BorelTransfer.lean)

Suppose $p^N T_1(a,R)(p)\to0$ along $p>0$ for every nonnegative integer $N$. The integral is $O(1/p)$, hence $a=0$. If $R(u)=u^k g(u)$ with $g(0)\ne0$, then $p^{k+1}T_1(0,R)(p)\to k!g(0)$. Thus $R$ vanishes near zero. The identity theorem gives $R=0$ throughout the common domain. On a frequency ray $p=qx$ with $x>0$, both lateral equations hold for all sufficiently large $x$ whenever $\Re(qd_-),\Re(qd_+)>0$. Lean proves this last simultaneous statement as `transfer_both_on_ray`. [Watson estimate](../Laplace.lean) · [Transfer proof](../BorelTransfer.lean)

## Application to the cubic kernel

Put $s=e^{i\pi/4}\sigma$, so the physical temperature $t=-is^2$ is $\sigma^2$. In this coordinate $s^2d/ds=e^{i\pi/4}(-d/dp)$. The Borel germ is $B(u)=\widehat f(e^{i\pi/4}u)$ and its minor is $B'(u)$. In the original $s$ coordinate select $0<\delta<\pi/4$ and the directions $\pm\delta$. In the rotated coordinate these are $d_\pm=e^{i(\pm\delta-\pi/4)}$. Take $s=e^{-i\delta}/x$ for extraction. Then
\[
 p=e^{i(\pi/4+\delta)}x,\qquad pd_-=x,\qquad \Re(pd_+)=x\cos(2\delta)>0 .
\]
This geometry also puts the lower background on the ray used by the coefficient-separation theorem.

For the domain take a small disk about zero, of radius less than the first branch radius, together with narrow open wedges about $1,d_-,d_+$. Choose the wedges away from all four rotated cut directions. This union is connected through the disk and stable under contraction. The branches defined from the disk glue there. On compact subsets the tail of the defining series for $B$ is bounded by a constant times $\sum n^{-4}$. On each slightly wider wedge, the cubic equation bounds $K$ uniformly away from its branch value. Splitting at $n\asymp 1+|u|^{2/3}$ gives $B(u)=O(1+\log(2+|u|))$. Cauchy estimates on smaller wedges give exponential type for $B'$, including on the physical direction. For a convergent coefficient germ $h(\sigma)=\sum h_n\sigma^n$ with $|h_n|\le M R^{-n}$, its minor is entire and bounded by $(M/R)e^{|u|/R}$. Termwise Laplace integration recovers $h(1/p)$ sufficiently far on each selected frequency ray. Clear a common Laurent pole before introducing the coefficient leaves. [Cubic Borel series and coefficient field](main.tex) · [Lacunary-series asymptotics of Costin and Huang](https://arxiv.org/abs/0810.3027)

Here is where the input of all-orders flatness comes from on paper. Mellin inversion on $t>0$ gives the formal regular part after removing $\Gamma(4/3)t^{-1/3}+1/2$. Moving past arbitrarily many poles also gives the differentiated expansion because a fixed number of derivatives adds only polynomial growth in the contour ordinate. The zeta functional equation identifies these coefficients with the Taylor coefficients of $B$. For $T_1$, integrate a degree-$M$ Taylor approximation to its minor on $0\le u\le\epsilon$. Its remainder contributes $O(p^{-M-2})$, and the rest of the integral is exponentially small. For the $j$th negative derivative multiply the minor by $u^j$ and apply the same estimate. Each monomial integrates to its factorial moment. Consequently any polynomial in these jets has the expansion obtained by the formal operations. For a relation of the formal series every coefficient vanishes, giving the required flatness. This also covers a relation chosen *after* minimizing degree in the formal relation ideal. Such a relation need only annihilate the formal expansion. No assertion that it annihilates the physical function pointwise enters this step.

An independent positive-temperature derivation identifies the physical Borel sum with a single sine integral and gives the difference from the regularized cube sum as a normally convergent Airy series. Its fixed derivatives are flat, and its sign changes infinitely often. [Derivation and checks](physical-airysum.md)

## Arithmetic consequence

Strip the positive common factor from the actions and put $A_n=n\sqrt n$. For a squarefree $d$, multiply a putative rational relation $A_d=\sum_{m<d} c_m A_m$ by $\sqrt d$ and take normalized field trace to $\mathbb Q$ in a finite extension of $\mathbb Q$ containing the radicals. The left side becomes $d^2$. Every right-hand term has trace zero, since $dm$ is nonsquare for $0<m<d$ and $X^2-dm$ has zero linear coefficient. Indeed $dm=b^2$ would imply $d\mid b$ by squarefreeness and then $d\mid m$. This proves isolation even for signed rational coefficients, including for $d=1$ with an empty lower list.

Conversely, if $n=k^2m$ with $k\ge2$, then $A_n=k^3 A_m$. Thus **exactly the squarefree positive indices give actions that cannot be built from smaller actions with unrestricted repetitions**. A bound on the polynomial degree bounds the permitted number of summands and can leave additional actions isolated. For instance $A_4=8A_1$ and $A_{36}=A_9+A_{16}+A_{25}$ give genuine collisions of two different lengths. The squarefree indices already suffice for the infinite-root argument. [Arithmetic certificate](../CubicActions.lean)

There is an exact way to group nonlinear products. Factor each index as $n=dk^2$ with $d$ squarefree. Attach $k^3$ to coordinate $d$ and add these integer coordinates across a product. Two such products have the same exponential precisely when their coordinate vectors agree. To see necessity, subtract the two finite expansions and take the largest squarefree index with a nonzero coefficient. It would be a rational combination of smaller actions, which the trace argument rules out. For example the three factors with indices $9,16,25$ contribute $27+64+125=216$ to coordinate $1$, exactly the contribution of index $36$. This gives exact equality tests for grouping. The underlying rational independence of squarefree radicals is classical. [Besicovitch, 1940](https://academic.oup.com/jlms/article-abstract/s1-15/1/3/1015865)

## A summable bound after grouping

On the extraction ray write $1/s=h x$, $h=e^{i\delta}$ and $c=\cos\delta>0$. The cut density in the manuscript obeys $|J(v)|\le C v^{-1/2}$ for all $v>0$. On compact subsets of $\Re(1/s)>0$, the cut integrals and their derivatives converge normally in $n$ by exponential decay. Both lateral sums are holomorphic on the intersection of their convergence half-planes. Consequently their jump identity on positive $s$ extends to the connected intersection with $\Re(1/s)>0$, including the extraction ray sufficiently near zero. [Cut density estimate](../CubicJump.lean) · [Jump formula](main.tex)

For a fixed jet order $j$, write $y=1/s$, $a=\omega_n(1+v)$ inside the cut integral. The exact differentiated prefactor is
\[
 (-\partial_y)^j(y e^{-ay})=e^{-ay}(a^j y-j a^{j-1}).
\]
The second term is absent for $j=0$. After stripping $e^{-\omega_n h x}$ and changing variables to $u=\omega_n x v$, the remaining absolute integrals are bounded by fixed moments of $u^{-1/2}(1+u/\omega_1)^j e^{-cu}$ for $x\ge1$. Hence, with constants independent of $n$ and $x$,
\[
 |e^{\omega_n h x}\partial^j W_n|\le C_{j,\delta}\,x^{1/2}
             (1+\omega_n)^{j+1/2}/n .
\]
For a differential polynomial of jet order $J$ and degree $D$, clear the poles of the coefficients first. The finite collection of background jets and coefficient germs is bounded on the extraction tail by their directional expansions. For the remaining products use $K=D/2$ and reserve $1$ in the separation theorem. Set
\[
 h_n=(1+\omega_n)^{J+1/2}e^{-c\omega_n}/n .
\]
Each ordered tuple of at most $D$ wave indices has a summable budget proportional to the product of its $h_n$. The sum of budgets for length $k$ is proportional to $(\sum_n h_n)^k<\infty$. Assign each tuple's budget to its exact action group and sum within the group. This gives $\sum_A b_A<\infty$ and the required bound $|a_A(x)|\le b_A e^{cA} x^K$ after removal of the unit phase and the real exponential. A bounded action range admits only finitely many indices and tuples. This supplies an explicit majorant for the proposed regrouping on paper. Its Lean instantiation and the common-ray representations of the grouped coefficients remain open.

## Checks and remaining work

Euler’s minor $1/(1-u)$ gives $Y'+Y=1/p$ on both lateral rays, although their difference is $2\pi i e^{-p}$. Squaring gives $Z=Y^2$ and $p^2(Z'+2Z)^2=4Z$. Direct quadrature at $p=2.3\pm0.4i$ checks both nonlinear identities and the jumps of $Y,Y'$ using independent derivative integrals. In the cubic case, integration of the first four original kernel differences along fixed rays at $s=1.3e^{-i\pi/10}$ agrees with the Bessel formula through the second jet. Nonlinear control (numerical script omitted from this release) · Cubic control (numerical script omitted from this release)

The generic transfer and arithmetic isolation have Lean proofs. The cubic Mellin-to-kernel identification, analytic continuation and growth estimates for that specific infinite kernel still enter on paper. The remaining assembly must group the products of the differentiated infinite jump series by their exact actions and furnish the common-ray representations and summable envelope used by the separation theorem. The package does not yet derive Pak’s conjecture end to end. [Separation theorem and package scope](../LEAN_GUIDE.md)
