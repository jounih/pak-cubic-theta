# Recovering the first cubic action from four temperatures

The regularized cube sum has an exponentially small oscillatory residual \(E(p)\), with \(p=t^{-1/2}\). Its logarithmic derivative is singular at a zero of the residual. Four equally spaced samples recover the leading decay and oscillation frequencies even along sequences approaching these zeros. The calculation applies Prony’s classical two-exponential recurrence to the exact physical Airy expansion. [Physical source and bounds](physical-ray-verification.md) · [Potts and Tasche on Prony recovery](https://doi.org/10.1016/j.sigpro.2009.11.012)

Write the leading action as \(c=a+ib\), choosing either conjugate, and set \(s_j=E(p+jh)/\sqrt{p+jh}\) for \(0\le j\le3\). Assume \(h>0\) and \(0<|b|h<\pi\). Define
\[
 D=s_0s_2-s_1^2,\qquad
 S=\frac{s_0s_3-s_1s_2}{D},\qquad
 P=\frac{s_1s_3-s_2^2}{D}.
\]
Then \(-\log P/(2h)\to a\) and \(h^{-1}\arccos(S/(2\sqrt P))\to |b|\). At fixed admissible \(h\), both errors are \(O_h(p^{-2})\).

**Derivation.** Put \(r=e^{-ch}\). In the exact first Airy mode, write the complex amplitude at the first sample as \(z=C e^{-cp}A(cp)\), with the normalization in the [Kummer formula](../PakStokes/PhysicalKummer.lean). The normalized integral gives \(A(cp)=1+O(1/p)\). Differentiating its factor \((1+v/(2cp))^{-1/6}\) with respect to \(p\) gives a bound \(v/(12|c|p^2)\) along the positive ray, since the base has real part at least one. The gamma weight has finite first moment. Thus the change in the normalized amplitude across the four samples is \(O_h(p^{-2})\). Every higher mode has decay at least \(2^{3/2}a\), and their sum after factoring out this exponential is bounded for large \(p\) by the Kummer unit bound and cubic spacing. Uniformly over the four samples,
\[
 s_j=z r^j+\bar z\bar r^j+O_h(e^{-ap}p^{-2}).
\]
For the exact pair the determinant is \(|z|^2(r-\bar r)^2\), strictly negative and independent of the phase of \(z\). In particular \(e^{2ap}D\to-4|C|^2e^{-2ah}\sin^2(bh)\). The exact numerators are that determinant times \(r+\bar r\) and \(r\bar r\), respectively. The four sample errors perturb each determinant by \(O_h(e^{-2ap}p^{-2})\). Division yields the stated accuracy. The strict step condition selects the principal frequency in the inverse cosine and excludes a real repeated node. The derivation is on paper. Lean checks the physical wave representation underlying it.

**Physical test.** The test forms each input from the defining cube sum, the gamma term and independent sine-integral quadrature for the background. The Airy formula supplies a separate comparison. With \(h=1/5\) both recovered rates approach \(4.2865008905426\).

| Initial \(p\) | Relative decay error | Relative frequency error |
|---:|---:|---:|
| 5 | \(5.85\times10^{-5}\) | \(6.84\times10^{-5}\) |
| 10 | \(1.70\times10^{-5}\) | \(1.74\times10^{-5}\) |
| 20 | \(4.59\times10^{-6}\) | \(4.64\times10^{-6}\) |
| 40 | \(1.15\times10^{-6}\) | \(1.16\times10^{-6}\) |

All sixteen physical samples agreed with independent Airy evaluations to absolute error below \(10^{-30}e^{-ap}\) in the normalized signal. The calculation used 110 decimal digits. Absolute input error must shrink with the signal, which has lost about 74 decimal orders to exponential damping at \(p=40\). Four samples reduce the sampling requirement while high precision pays for the subtraction of the background. The test concerns an isolated leading conjugate pair in an exact-temperature series. Performance on noisy instrument waveforms would require its own benchmark. Reproducible test (numerical script omitted from this release)
