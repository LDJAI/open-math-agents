# Can bounded degree prevent a large parametric min-cut path?

[Left To Solve](https://lefttosolve.com/p/mo-76075) · [Original question, September 21, 2011](https://mathoverflow.net/questions/76075/number-of-breakpoints-in-parametric-maximum-flow-problems)

For binary variables, consider the minimum over configurations of a quadratic energy with affine unary costs and constant nonpositive pair coefficients. A breakpoint is a parameter at which the minimum fails to agree with any affine function on any open neighborhood. Count neighbors in the undirected interaction graph, so reversing the order of a coefficient cannot make the graph appear sparser.

**Construction.** For every nonnegative integer r, a degree-three instance with (2r+1)² variables has at least 2ʳ − 1 breakpoints. This rules out every polynomial in the number of variables at fixed degree. It is a worst-case statement about tracing the entire value curve. A single specified parameter still gives an ordinary graph-cut optimization.

### Doubling the number of active cuts

Begin with one bit whose unique optimum is zero. Given an instance E(x,t) with unary slopes bᵢ, add two bits u and v. Write Nᵢ = 2 min(bᵢ,0) and Pᵢ = −2 max(bᵢ,0). Replace the old unaries by aᵢ − Nᵢ + 3tbᵢ, add the interactions Nᵢxᵢu + Pᵢxᵢv, and add the switch costs H(t−1/2)u + H(1/2−t)v, with H = 12(1+Σᵢ |bᵢ|). All new pair coefficients are nonpositive.

For t in the first third of the unit interval, every optimizer has (u,v) = (1,0). The switch preference has magnitude at least H/6, while incident terms can change it by at most 2Σᵢ |bᵢ|. The restricted energy is E(x,3t) plus a common affine term. In the last third the switches are (0,1); the restricted energy is E(x,3t−2) plus a common affine term. Therefore every old uniquely optimal configuration gives two new uniquely optimal configurations on disjoint intervals. After r doublings there are at least 2ʳ on 2r+1 bits.

### Keeping three neighbors per bit

For n dense bits use n² sites indexed by ordered pairs (i,j). Place each original unary on (i,i) and the interaction cᵢⱼ between (i,j) and (j,i). For each first index i, join the copies in a cycle and charge M for disagreeing adjacent bits, where M = 1 + Σᵢⱼ |cᵢⱼ|. The disagreement cost M(y+z−2yz) is itself an admissible unary-plus-attractive-pair expression. A site has at most two cycle neighbors and its transpose.

Round every row to the value of its diagonal bit. Rounding leaves every unary intact. If the row was nonconstant, at least one disagreement disappears and all rows are now constant. The loss on the original pair terms is bounded by Σ |cᵢⱼ| < M. Thus every optimizer is constant on rows, and the minimum and its entire value curve are preserved for all parameter values.

### Why configurations give genuine breakpoints

At a strict minimum, finitely many strict inequalities remain strict on a neighborhood, so the value locally equals the affine energy of that configuration. Two distinct configurations strictly optimal at different parameters must give different slopes: parallel affine functions cannot strictly undercut each other in opposite orders. Ordering M distinct slopes by points where they occur gives at least M−1 breakpoints between successive points.

### Prior work and scope

Kolmogorov, Boykov and Rother (2007) describe dense parametric graph-cut lower bounds in the computer-vision setting. Choi (2008) studies strong ferromagnetic couplings for graph minor embeddings. Gajjar and Radhakrishnan give a lower bound for planar parametric cuts, discussed in the 2025 survey by Nemesch, Ruzika, Thielen and Wittmann. These results make a bounded-degree obstruction plausible through other reductions. We found no explicit resolution of the particular bounded-neighbor, fixed-pair-coefficient question in this search. We claim no priority for parametric-flow lower bounds or for identifying variables with large equality penalties.

[Kolmogorov, Boykov and Rother](https://cs.uwaterloo.ca/~yboykov/Papers/iccv07_par_maxflow.pdf) · [Choi](https://arxiv.org/abs/0804.4884) · [Parametric optimization survey](https://doi.org/10.1007/s10898-025-01512-6)
