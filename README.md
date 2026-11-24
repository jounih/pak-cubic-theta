# Differential transcendence of the cubic theta series

Igor Pak’s Conjecture 2.6 asks whether the formal power series
$H(q)=\sum_{n\ge 0} q^{n^3}=1+q+q^8+q^{27}+\cdots$
is differentially transcendental. The proof here establishes the conjecture over the complex rational function field. [Pak, *Complexity problems in enumerative combinatorics*, Conjecture 2.6, arXiv:1803.06636](https://arxiv.org/abs/1803.06636)

Machine-checked by the Lean kernel; independent specialist review welcome. Developed with substantial AI assistance.

## Statement

In namespace `CubicTheta` the theorem reads

```lean
theorem pak_conjecture_2_6 : AlgebraicIndependent ℂ Nome.coordinates
```

The ambient ring is `PowerSeries ℂ`. The coefficient of degree $k$ in `Nome.H` is one precisely when $k$ is a nonnegative integer cube, and zero otherwise. `Nome.jet j` applies the ordinary formal derivative $j$ times to `Nome.H`. The zeroth coordinate of `Nome.coordinates` is the series variable $q$ itself, and coordinate $j+1$ is `Nome.jet j`. [Theorem](PakStokes.lean) · [Definitions](PakStokes/CubeNome.lean)

An algebraic differential equation over $\mathbb C(q)$ would be a nonzero polynomial relation in finitely many derivatives with rational functions of $q$ as coefficients. Clearing their denominators would give a nonzero polynomial over $\mathbb C$ in $q,H,H',\ldots$. Algebraic independence of the stated coordinates excludes every such relation.

## Proof

1. Evaluate the series at $q=e^{-1/p^2}$ for $p>0$ and remove the explicit endpoint and gamma terms.
2. Use Poisson summation and an Airy integral to express the regularized sum as a background and two families of exponentially small waves.
3. Differentiate the convergent expansion and group products by their complex exponential rates. Laplace kernel estimates force each group of a zero identity to vanish.
4. Write each positive wave index as $d k^2$ with $d$ squarefree. Mark its sign and squarefree part by a formal variable raised to the power $k^3$. Equal rates then correspond exactly to equal monomials.
5. For $J$ derivatives choose $J$ distinct prime marks. The scaled matrix of fundamental wave amplitudes tends to an invertible Vandermonde matrix.
6. Differentiating a polynomial relation in the marks would give relations of lower degree, contradicting minimality.
7. A putative equation for the original formal series would give an autonomous equation for the regularized sum by a local change of variable, finite-dimensional polynomial elimination and analytic continuation.

[Proof and controls](paper/marked-wave-proof.md) · [Change of variable](PakStokes/PakTransfer.lean) · [Module guide](LEAN_GUIDE.md)

## Verification

With Lean’s toolchain manager installed, run these commands at the repository root. The Lean toolchain and mathlib revision are pinned.

```sh
lake exe cache get
lake build
lake env lean Verify.lean
```

The last command prints the theorem type, the definitions and the axioms. Its expected final line is

```text
'CubicTheta.pak_conjecture_2_6' depends on axioms: [propext, Classical.choice, Quot.sound]
```
