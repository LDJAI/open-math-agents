# A unique worst noise variance for pooling scalar Gaussian updates

**Left to Solve mo-204379.** [Catalog listing](https://lefttosolve.com/p/mo-204379) · [MathOverflow question, April 30, 2015](https://mathoverflow.net/questions/204379/maximizing-the-discrepancy-in-jensens-inequality-for-a-certain-function). The dated source asks whether the Jensen gap below has a single maximum as its parameter varies. The site’s upstream MathOverflow data file is `data/extra3.json.gz`, row 204379. The public question was indexed as unanswered. Searches by title, equation, harmonic sum, and Jensen-gap unimodality found no earlier proof of this particular result. That search cannot establish priority.

## Theorem

Let $b_1,\dots,b_n$ be positive, with at least two distinct values. Write $m=n^{-1}\sum_i b_i$ and $f_a(b)=ab/(a+b)$. The function

$$D(a)=n f_a(m)-\sum_{i=1}^n f_a(b_i),\qquad a>0,$$

is strictly increasing up to a unique $a_*>0$ and strictly decreasing after it. Its maximum is positive. The original first term, $(1/(na)+1/(\sum_i b_i))^{-1}$, equals $n f_a(m)$.

## Proof

Make the increasing change of variables $t=a/(a+m)$, from $(0,\infty)$ onto $(0,1)$. Let $k_i=m/b_i-1$, so $k_i>-1$. Direct substitution gives

$$d(t):=\frac{D(a)}{m}=nt-\sum_i\frac{t}{1+k_i t}.$$

This function extends smoothly across $[0,1]$ and $d(0)=d(1)=0$, since $1/(1+k_i)=b_i/m$. Hence Rolle’s theorem supplies $t_*\in(0,1)$ with $d'(t_*)=0$. To prove that this is the only critical point, factor the derivative:

$$d'(t)=\sum_i\left(1-\frac{1}{(1+k_i t)^2}\right)=t\,G(t),\qquad
G(t)=\sum_i\frac{k_i(2+k_i t)}{(1+k_i t)^2}.$$

Termwise differentiation now gives

$$G'(t)=-\sum_i \frac{k_i^2(3+k_i t)}{(1+k_i t)^3}<0\qquad (0\leq t\leq 1).$$

Every denominator is positive, every $3+k_i t$ is positive, and at least one $k_i$ is nonzero. Thus $G$ is strictly decreasing, crossing zero only at $t_*$. Consequently $d$ strictly increases before $t_*$ and strictly decreases afterwards. The two zero endpoint values imply positivity throughout the interior. The change of variables preserves this shape and gives $a_*=mt_* /(1-t_*)$. This proves the conjecture for every admissible list.

## Computing the maximum

Solve the one-dimensional strictly decreasing equation $G(t_*)=0$ on $[0,1]$. The maximum value is explicitly characterized by $D_{\max}=m(nt_*-\sum_i t_* /(1+k_i t_*))$. Interval bisection gives an error at most $2^{-s}$ in $t_*$ after $s$ steps. With rational inputs, all bisection comparisons can use exact rational arithmetic. Clearing the positive denominators gives a polynomial equation, with exactly one root in $(0,1)$. The constant-input case, excluded in the question, has $D\equiv0$.

## A consequence for state estimation

For a scalar Gaussian observation with measurement-noise variance $a$ and prior variance $b$, the posterior variance is $ab/(a+b)$. If a batch has different known prior variances, but a summary replaces them by their mean, the estimated total posterior variance exceeds the sum computed from the individual updates by exactly $D(a)$. The theorem identifies a unique measurement-noise variance where this aggregation error is largest. The same argument works for arbitrary positive finite weights: use the weighted mean and weight every summand, including each summand of $G'$. [Scalar Kalman update equations, University of Michigan](https://www.eecs.umich.edu/courses/eng100/lec1/kalman.html)

This comparison concerns averaging variances before distinct scalar updates. A common unknown variance or a mixture posterior has a different statistical model.
