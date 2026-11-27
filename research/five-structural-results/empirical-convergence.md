# A simultaneous law of large numbers with no countable Glivenko–Cantelli cover

Alexander R. Pruss asked in 2012 whether every class of sets satisfying a simultaneous strong law on a Polish space is a countable union of Glivenko–Cantelli classes. The answer is **no, even for a family of compact countable subsets of the unit interval**. A single reference distribution, Lebesgue measure, witnesses the failure of every possible countable decomposition. [Pruss's original question](https://mathoverflow.net/questions/107177/simultaneous-strong-law-of-large-number-classes) · [Left to Solve](https://lefttosolve.com/p/mo-107177)

For iid observations with law $P$, write $P_n(A)=n^{-1}\sum_{i=1}^n\mathbf1_A(X_i)$. A class has the *simultaneous strong law* when, for every $P$, there is a measurable event of probability one on which $P_n(A)\to P(A)$ for every member $A$. A class is *Glivenko–Cantelli for $P$* when, on such an event, the supremum over its members of $|P_n(A)-P(A)|$ tends to zero. It is *universally Glivenko–Cantelli* when this holds for every $P$.

## The construction

Partition $(0,1]$ into the intervals $I_j=(2^{-j},2^{1-j}]$ for $j\ge1$. Consider

$$
\mathcal C=
\left\{\{0\}\cup\bigcup_{j\ge1} F_j:
                F_j\subseteq I_j\text{ is finite for each }j\right\}.
$$

Every member is countable and compact. On any closed subinterval bounded away from zero it has only finitely many points, and zero is included.

**Theorem.** The class $\mathcal C$ satisfies the simultaneous strong law for every Borel probability measure on $[0,1]$. It has no countable cover by classes that are Glivenko–Cantelli for Lebesgue measure.

**Proof of simultaneous convergence.** Fix $P$. Its set of point atoms $D=\{x:P\{x\}>0\}$ is countable. By the scalar strong law on a single probability-one event, all empirical frequencies of points of $D$ converge correctly, and so do the empirical frequencies of each tail $T_J=(0,2^{-J}]$. With probability one no two draws coincide outside $D$, since for $r\ne s$,

$$\Pr(X_r=X_s\notin D)=\int_{[0,1]\setminus D}P(\{x\})\,dP(x)=0.$$

Intersect these countably many events. On the resulting event, empirical probabilities converge simultaneously for **every finite set** $F$. This follows by summing the point frequencies: every nonatom appears at most once, and the frequencies of every atom converge.

For any $A\in\mathcal C$, the set $A\setminus T_J$ is finite. Consequently, on this same event,

$$
\limsup_{n\to\infty}|P_n(A)-P(A)|
\le\limsup_{n\to\infty}\max\{P_n(T_J),P(T_J)\}=P(T_J).
$$

The tails decrease to the empty set, so $P(T_J)\downarrow0$. There was no choice of the event depending on $A$.

**Proof against every countable cover.** Suppose $\mathcal C$ were covered by $\mathcal G_1,\mathcal G_2,\ldots$, each Glivenko–Cantelli for Lebesgue measure $L$. Intersect each class with $\mathcal C$. This preserves the cover and can only decrease the suprema. Every remaining member has $L$-measure zero.

For a fixed $j$, the traces $\{A\cap I_j:A\in\mathcal G_j\}$ must omit some finite subset $F_j\subseteq I_j$. Otherwise, for every finite sample there would be a member whose trace equals the set of sampled points in $I_j$. Therefore

$$
\sup_{A\in\mathcal G_j}|P_n(A)-L(A)|\ge P_n(I_j)\longrightarrow L(I_j)=2^{-j}>0
$$

almost surely under Lebesgue sampling, contradicting the Glivenko–Cantelli property. Select one missing trace $F_j$ for each $j$. Then $A=\{0\}\cup\bigcup_j F_j$ belongs to $\mathcal C$ and differs on $I_j$ from every member of $\mathcal G_j$, simultaneously for all $j$. This contradicts the cover. ∎

The complete class even has uniform discrepancy exactly one at every sample size under Lebesgue measure: it contains a member consisting of zero together with the observed sample. The theorem shows why splitting the class into countably many pieces cannot restore uniform control.

## The countable partition criterion

There is a general reason this example works. Let a standard Borel space $X$ be partitioned into countably many nonempty Borel sets $X_j$. For each $j$ take a nonempty class $\mathcal F_j$ of Borel subsets of $X_j$, and allow the choices on different parts to be independent:

$$
\mathcal F=\left\{\bigcup_{j\ge1} A_j:A_j\in\mathcal F_j\text{ for every }j\right\}.
$$

Then $\mathcal F$ is a countable union of universally Glivenko–Cantelli classes **if and only if** every $\mathcal F_j$ is a countable union of such classes on $X_j$, and all but finitely many $\mathcal F_j$ are already universally Glivenko–Cantelli individually. The simultaneous strong law holds for $\mathcal F$ if and only if it holds for each $\mathcal F_j$.

**Proof.** Under any law $P$, the empirical mass of every part and each tail of parts converges to its true mass on one event. Whenever $P(X_j)>0$, the sequence of observations that land in $X_j$ is iid with the conditional law on that part. This follows by conditioning on its successive hit times and using independence of the original draws. A part of zero probability receives no observations almost surely. Intersecting the resulting countably many probability-one events yields convergence on every part, either simultaneous or uniform as appropriate. The error over the parts after $J$ is bounded by the larger of the empirical and true tail mass. Summing the first $J$ errors and letting $J$ tend to infinity proves that the product of simultaneous classes is simultaneous, and that the product of universally Glivenko–Cantelli classes is universally Glivenko–Cantelli. Necessity for the simultaneous assertion follows by choosing a law concentrated on one part.

Suppose the product has a countable universally Glivenko–Cantelli cover. Project the cover to traces on any one part. Sampling from laws supported there shows these traces give a countable universally Glivenko–Cantelli cover of the factor. If there were infinitely many factors failing the universal Glivenko–Cantelli property, assign a different failing factor to each covering class. Its traces on that factor must miss a member, since all of its traces are universally Glivenko–Cantelli. Combining the missed members produces one product member outside the cover. Conversely, choose a class from a countable cover of each of the finitely many exceptional factors. There are only countably many such finite choices. Each resulting product class is universally Glivenko–Cantelli by the preceding tail argument. ∎

## Verification

The accompanying Lean file checks the deterministic negative theorem on a sample stream encoded by its block number and value. Given strictly positive limiting block frequencies and vanishing uniform upper bounds on the empirical masses of each proposed covering class, the file constructs a classifier outside all of them. It also checks the real-sequence truncation estimate in the positive proof. The scalar strong-law applications, the nonatomic no-repeat argument and the abstract partition criterion are proved in the text. All four checked declarations use the standard Lean axioms listed in the compilation log. [Lean source](PrussCertificate.lean) · [Compilation log](PrussCertificate.log)

## Context and limits of the claim

Pruss earned his mathematics PhD at the University of British Columbia. He wrote, “I suppose it would be too much to hope for if every SSLLN class was a countable union of GC classes.” The counterexample confirms that doubt. The 2012 question also asked about established terminology. We resolve its mathematical implication and give a sufficient-and-necessary condition for classes formed by independent choices on countably many parts. [Original discussion](https://mathoverflow.net/questions/107177/simultaneous-strong-law-of-large-number-classes) · [Baylor University biography](https://artsandsciences.baylor.edu/news/story/2025/baylor-philosopher-honored-excellence-teaching-and-scholarship)

For statistical learning, the two quantifier orders concern whether the empirical behavior of a data-selected member is controlled. Every member in the example eventually has the right frequency on the same infinite data stream. At each finite sample size, choosing a member after observing the data can nevertheless yield error one. This statement concerns empirical probabilities of sets.

Ramon van Handel characterized universally Glivenko–Cantelli classes under separability and standard-space hypotheses. Bousquet, Hanneke, Moran, van Handel and Yehudayoff compared rates of universal classification learning with countable unions of finite-VC classes, including a distinct counterexample in their Example 2.7. Those are related properties. A search of the original thread, its title and author, the empirical-process literature, and the terms “countable union of Glivenko–Cantelli classes” and “simultaneous strong law” found no earlier statement of this counterexample or the partition criterion. The original thread displayed no posted answer. These checks leave independent publication priority unverified. [Van Handel, 2013](https://doi.org/10.1007/s00440-012-0416-5) · [Bousquet et al., Example 2.7](https://arxiv.org/abs/2011.04483)
