# An additive comparison of Gaussian change-point locations

## Result

Let $d>0$, let $B$ be two-sided standard Brownian motion with independent branches, and set
$$
D=\operatorname*{argmax}_{n\in\mathbb Z}(B_n-d|n|),\qquad
T=\operatorname*{argmax}_{t\in\mathbb R}(B_t-d|t|).
$$
The following comparison concerns the two marginal laws. There is a computable number $b_d<\infty$ and a coupling of these laws in which $|D-T|\le b_d$ almost surely. Consequently, for any $a>0$,
$$
  D\le_{\rm st} aT+b\text{ for some }b\in\mathbb R
    \quad\Longleftrightarrow\quad a=1.
$$
Neither signed law stochastically dominates the other with zero shift. If $r_\alpha$ is any radius with $\Pr(|T|>r_\alpha)\le\alpha$, then $\Pr(|D|>r_\alpha+b_d)\le\alpha$. This transfers every confidence level using the same drift-dependent correction. The construction provides a conservative bound, with no optimality or uniformity in $d$ asserted.

Elena Yudovina asked for such a comparison on September 22, 2013. Her initial parenthetical was “Stochastic domination seems unlikely.” She subsequently asked for an affine stochastic bound and said an affirmative answer would help construct conservative confidence intervals. Martin Hairer and Ofer Zeitouni discussed the distance between the two maximizers observed on the same sample path. Zeitouni then predicted an affirmative answer with drift-dependent constants and suggested a factor of two would suffice by symmetry. The theorem confirms Yudovina's initial doubt about the unshifted signed order, settles her edited question affirmatively, and shows why a multiplier larger than one fails on the negative tail. The coupling constructed below permits a different joint law from observing both maximizers on the same trajectory. [Original question and full discussion](https://mathoverflow.net/questions/142880/argmax-of-random-walk-vs-of-brownian-motion) · [Yudovina's Cambridge mathematics doctorate](https://www.aapt.org/physicsteam/2025/upload/Elena-Yudovina-Bio.pdf)

Left to Solve catalogs the question under Probability and Operator Theory as `mo-142880`. Its source dataset records the September 2013 posting, and the original discussion contains comments but no posted answer at the time checked. [Catalog entry](https://lefttosolve.com/p/mo-142880) · [Registry dataset](https://github.com/LDJAI/open-math-agents/blob/main/data/extra3.json.gz)

## Discrete tail

Put $\lambda=d^2/2$ and $H(t)=e^{-\lambda t}(1+t)^{-3/2}$. On one arm write $S_n$ for the sum of $n$ independent $N(-d,1)$ increments, and set
$$
 q=\Pr(S_j<0\text{ for every }j\ge1),\qquad
 h_n=\Pr(S_1>0,\ldots,S_n>0).
$$
Here $q\ge q_*:=\Phi(d-1)(1-e^{-2d})>0$, since we may require the first step to be below $-1$ and then require the future continuous drifted Brownian increment process never to reach 1. Indeed its all-time maximum is exponential of rate $2d$.

For $n\ge1$, time $n$ is a strict record relative to $0,\ldots,n-1$ with probability $h_n$ by reversing the first $n$ increments. For this to give the global maximizer, the future walk must stay below its value at $n$, an independent event of probability $q$, and the maximum of the other arm must lie below $S_n$. Conditional on the record this last probability lies between $q$ and 1 since $S_n>0$. Thus
$$
 q^2 h_n\le \Pr(D=n)\le q h_n.
$$
The maximum time is almost surely unique since distinct sampled values have a continuous difference and both arms tend to negative infinity. By independence of the arms, $\Pr(D=0)=q^2$.

The Sparre Andersen factorization for continuous increments gives, as a power series with $h_0=1$,
$$
 \sum_{n\ge0}h_nz^n=
 \exp\left(\sum_{j\ge1}\frac{\bar\Phi(d\sqrt j)}{j}z^j\right).
$$
This is the classical identity for survival probabilities, applied after reversing signs. [Formula and original reference](https://link.springer.com/article/10.1007/s10955-025-03560-4)

Let $a_j=e^{\lambda j}\bar\Phi(d\sqrt j)/j$. The Gaussian Mills bounds $x\phi(x)/(1+x^2)\le\bar\Phi(x)\le\phi(x)/x$ imply
$$
 A_-j^{-3/2}\le a_j\le A_+j^{-3/2},\qquad
 A_-=\frac{d}{\sqrt{2\pi}(1+d^2)},\quad
 A_+=\frac1{d\sqrt{2\pi}}.
$$
For $u_j=j^{-3/2}$ on the positive integers and zero elsewhere, splitting the convolution sum at $n/2$ gives $(u*u)_n\le Ku_n$ with $K=2^{5/2}\zeta(3/2)$. For each summand in one half, the larger index contributes at most $(n/2)^{-3/2}$, and the other factors sum to at most $\zeta(3/2)$. Thus $u^{*k}\le K^{k-1}u$ for $k\ge1$. In the exponential generating identity, the linear term bounds each positive-index coefficient from below. Summing the bounds on its ordinary convolution powers yields
$$
 A_-n^{-3/2}\le e^{\lambda n} h_n\le A_h n^{-3/2},\qquad
 A_h=\frac{\exp(K A_+)-1}{K}.
$$
With $n_0=\lfloor t\rfloor+1$, retain the $n_0$ term for a lower bound and sum a geometric series for the upper bound. Since $n_0\le1+t\le2n_0$, symmetry of the arms gives, for every $t\ge0$,
$$
 2q_*^2 A_-e^{-\lambda}H(t)
 \le \Pr(|D|>t)
 \le \frac{2^{5/2} A_h}{1-e^{-\lambda}}H(t). \tag{1}
$$

## Continuous tail

For one branch of drifted Brownian motion write $M$ for its all-time maximum and $V$ for the time attaining that maximum. Their joint density at $m,s>0$ is
$$
 \frac{2dm}{\sqrt{2\pi}s^{3/2}}\exp\left(-\frac{(m+ds)^2}{2s}\right).
$$
For completeness, the unconditioned hitting-time density of the level $m$ is $m\exp(-(m+ds)^2/(2s))/(\sqrt{2\pi}s^{3/2})$, by the Brownian reflection formula and change of drift. After hitting $m$, the chance of never reaching $m+\varepsilon$ is $1-e^{-2d\varepsilon}$ by the strong Markov property. To pass to the joint density, approximate $M$ from below by the largest dyadic mesh point it exceeds. The first hitting time of that point tends to $V$ almost surely by continuity and uniqueness of the maximizer. Testing against compactly supported continuous functions of $(m,s)\in(0,\infty)^2$ now gives the stated density by Riemann sums. Each branch has strictly positive maximum, and its exponential law is continuous. The maximum times within branches are almost surely unique, as for Brownian motion on compact intervals. Both maxima are attained at finite times by negative drift.

By independence of the other arm, its maximum is below $m$ with probability $1-e^{-2dm}$. Hence the density of the signed location $T$ at $s>0$ is
$$
 f(s)=\frac{2d}{\sqrt{2\pi}}s^{-3/2}e^{-\lambda s}
 \int_0^\infty m e^{-dm-m^2/(2s)}(1-e^{-2dm})\,dm.
$$
For $s\ge1$, dropping the Gaussian factor bounds the integral above by $8/(9d^2)$. Restricting to $1\le m\le2$ bounds it below by $e^{-2d-2}(1-e^{-2d})$. Set
$$
 b_- =\frac{2d}{\sqrt{2\pi}}e^{-2d-2}(1-e^{-2d}),\qquad
 b_+ =\frac{16}{9d\sqrt{2\pi}}.
$$
Then $b_-s^{-3/2}e^{-\lambda s}\le f(s)\le b_+s^{-3/2}e^{-\lambda s}$ for $s\ge1$. For $t\ge1$, integration on $[t,t+1]$ gives $\Pr(|T|>t)\ge2b_-e^{-\lambda} H(t)$. Integration on $[t,\infty)$ gives $\Pr(|T|>t)\le 2^{5/2}b_+H(t)/\lambda$. For $0\le t\le1$, sandwich the probability between the lower bound at $t=1$ and 1. We obtain, for every $t\ge0$,
$$
 2b_- e^{-2\lambda}2^{-3/2}H(t)\le \Pr(|T|>t)\le
 \max\{2^{5/2}b_+/\lambda,\,2^{3/2} e^{\lambda}\}H(t). \tag{2}
$$

## Coupling and necessity

Choose $L$ as the smaller of the two lower constants in (1) and (2), and $U$ as the larger of their upper constants. Define
$$
 b_d=\lambda^{-1}\log(U/L).
$$
Since $H(t+b_d)\le e^{-\lambda b_d}H(t)$, equations (1) and (2) imply, for every $t\ge0$,
$$
 \Pr(|D|>t+b_d)\le\Pr(|T|>t),\qquad
 \Pr(|T|>t+b_d)\le\Pr(|D|>t).
$$
Thus $|D|\le_{\rm st}|T|+b_d$ and $|T|\le_{\rm st}|D|+b_d$. Applying their generalized-inverse distribution functions to the same uniform random variable couples the magnitudes at distance at most $b_d$. Attach the same independent symmetric sign to both. This preserves the respective marginal laws including the discrete mass at zero, and bounds the signed distance by $b_d$ as well.

To prove necessity let $D\le_{\rm st}aT+b$, where $a>0$ and $b$ is finite. Equations (1) and (2) and symmetry give $\lim_{t\to\infty}t^{-1}\log\Pr(X>t)=-\lambda$ for $X=D,T$, and the same rate for $\Pr(X\le-t)$, since shifting the tail threshold by one handles equality at integer times. On the right the order forces $-\lambda\le-\lambda/a$, hence $a\ge1$. On the left it forces $-\lambda\ge-\lambda/a$, hence $a\le1$. This proves necessity. Symmetry would extend the statement to $|a|=1$ if negative multipliers are allowed. For raw domination, both variables have finite mean zero. A quantile coupling of two ordered integrable variables with equal means yields equality almost surely. Here the laws differ at zero since $D$ has mass $q^2>0$, while $T$ has no atom. This rules out both directions at zero shift.

## Prior work and scope

The continuous marginal law and exact expressions for the discrete marginal were published before the question. Yao's Brownian approximation and Stryhn's extension are part of the change-point literature. Fotopoulos, Jandhyala and Khapalova give the exact limiting change-point law in the Gaussian model. Chen, Wang and Samworth's Lemma 6 also bounds one-sided continuous and discrete maximizer tails, with unequal lower and upper exponential rates. Neither such rate bounds nor convergence in distribution alone imply a uniformly bounded difference across quantiles. The specific comparison above uses the matching polynomial factor as well as the matching exponential factor. I found no earlier explicit statement of the additive bounded-distance coupling or full signed affine classification in these sources or the indexed literature searched. This is a proposed mathematical resolution, without independent publication or peer review, and the priority search is necessarily incomplete.

* [Yao (1987), *Approximating the distribution of the maximum likelihood estimate of the change-point in a sequence of independent random variables*](https://doi.org/10.1214/aos/1176350509)
* [Stryhn (1996), *The location of the maximum of asymmetric two-sided Brownian motion with triangular drift*](https://doi.org/10.1016/0167-7152(95)00183-2)
* [Fotopoulos, Jandhyala and Khapalova (2010), *Exact asymptotic distribution of change-point MLE for change in the mean of Gaussian sequences*](https://arxiv.org/abs/1011.2322)
* [Chen, Wang and Samworth, *High-dimensional, multiscale online changepoint detection*, Lemma 6](https://personal.lse.ac.uk/wangt60/publication/ocd.pdf)
