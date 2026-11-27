# Which lengths can the parallel slices of a smooth graph have?

Arnaud Chéritat asked this question for continuously differentiable functions on the unit square on 15 October 2014. “Hence I do not expect L to always be a C¹ function of y.” He asked how irregular the length can be. The range theorem below settles the regularity question and confirms his stated expectation. See [the original question and its comments](https://mathoverflow.net/questions/184507) and [Chéritat’s curriculum vitae](https://www.math.univ-toulouse.fr/~cheritat/CV-court-2022.pdf).

## Theorem

For a real function $f$ of class $C^1$ on $[0,1]^2$, define the length of its horizontal graph slice by
$$L_f(y)=\int_0^1 \sqrt{1+f_x(x,y)^2}\,dx.$$
The set of possible $L_f$ is exactly the set of continuous functions from $[0,1]$ to $[1,\infty)$. Every such profile is realizable with both $f(0,y)=0$ and $f(1,y)=0$. In particular one can prescribe $1+|y-1/2|$, or any continuous nowhere-differentiable profile taking values above one.

## Proof

The integrand is continuous on the compact square and at least one. Integration against $x$ gives a continuous function of $y$ bounded below by one.

Conversely let $L$ be such a profile and let $h=L-1$. We first express $h$ as a uniformly convergent series $\sum_{j\ge1}g_j^2$ of squares of smooth nonnegative functions. For a nonnegative continuous residual $r$, approximate $\sqrt r$ uniformly within $\delta>0$ by a polynomial $u$. Choose a nonnegative smooth function of integral one supported in $(0,\delta)$ and convolve it with the positive-part function to obtain $\psi$. Then $t_+-\delta\le\psi(t)\le t_+$. Set $g=\psi(u-\delta)$. We have $0\le g\le\sqrt r$ and $\|\sqrt r-g\|_\infty\le3\delta$. Hence $0\le r-g^2$ can be made arbitrarily small uniformly. Starting at $r_0=h$, choose $g_j$ so $r_j=r_{j-1}-g_j^2$ satisfies $\|r_j\|_\infty\le4^{-j}$. In particular $\|g_j\|_\infty\le2^{-(j-1)}$ for $j\ge2$.

Write $w_j=2^{-j}$ and $a_j=1-2^{1-j}$. These consecutive intervals $[a_j,a_j+w_j]$ fill $[0,1)$ up to their common endpoints. Define
$$\Phi(b)=\int_0^1\big(\sqrt{1+b^2\sin^2(2\pi t)}-1\big)\,dt,\qquad
\rho(b)=\operatorname{sgn}(b)\sqrt{\Phi(b)},\quad \rho(0)=0.$$
Rationalizing the integrand gives $\rho(b)=b\sqrt{\int_0^1 \sin^2(2\pi t)/(1+\sqrt{1+b^2\sin^2(2\pi t)})\,dt}$. It follows that $\rho$ is smooth and $\rho'(0)=1/2$. Differentiating $\Phi$ shows $\rho'(b)>0$ elsewhere. As $|b|\to\infty$, $\Phi(b)\ge |b|\int_0^1|\sin(2\pi t)|dt-1\to\infty$. Thus $\rho$ has a smooth inverse on the real line.

On band $j$ use the smooth amplitude $b_j(y)=\rho^{-1}(g_j(y)/\sqrt{w_j})$. The bound above implies $\|b_j\|_\infty\to0$. Each derivative $b_j'$ is bounded on the unit interval. Choose an integer $N_j\ge1$ large enough that $w_j\|b_j'\|_\infty/(\pi N_j)\le2^{-j}$. For $x$ in band $j$, put
$$f(x,y)=\frac{w_j b_j(y)}{2\pi N_j}\left[1-\cos\left(\frac{2\pi N_j(x-a_j)}{w_j}\right)\right],\qquad f(1,y)=0.$$

The function and both first partial derivatives vanish on every seam. Inside band $j$, $f_x$ is $b_j(y)$ times the sine of the phase, and $|f_y|\le2^{-j}$. These partials thus converge uniformly to zero at the accumulating edge. There $f_y=0$ because $f(1,y)=0$. Since $1-x\ge w_j$ on band $j$, one also has $|f(x,y)|/(1-x)\le\|b_j\|_\infty/(\pi N_j)\to0$, verifying $f_x(1,y)=0$. This gives $C^1$ regularity up to the boundary. Equivalently, a $C^1$ extension across the square can be obtained by first-order reflection in its edges.

Each band contains an integer number of full oscillations. Its contribution to the slice length is exactly $w_j[1+\Phi(b_j(y))]=w_j+g_j(y)^2$. Summing gives $1+h(y)=L(y)$, as required.

## Status

This construction is a mathematical proof in prose. The accompanying Lean file checks the necessary conditions of continuity and the lower bound of one. It does not check the construction. The cited 2014 discussion mentions a related forum problem about surface intersections. A result about arbitrary intersections with tangent planes does not directly establish the parallel, transverse graph-slice theorem here. No assertion of global publication priority is made.
