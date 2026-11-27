from itertools import product, combinations
from collections import Counter
def check(n, x):
    w=n+1
    hs=[(y*w+i,y*w+i+1) for y in range(w) for i in range(n)]
    vs=[(j*w+i,(j+1)*w+i) for j in range(n) for i in range(w)]
    universe=set(hs+vs)
    res={}
    for a,b in [(1,2),(2,1)]:
        total=hits=0
        for H,V in product(combinations(hs,a),combinations(vs,b)):
            adj=[[] for _ in range(w*w)]
            for i,j in universe.difference(H,V):
                adj[i].append(j);adj[j].append(i)
            seen={0};queue=[0]
            for v in queue:
                for u in adj[v]:
                    if u not in seen:seen.add(u);queue.append(u)
            total+=1
            hits+=x[0]+w*x[1] in seen
        res[(a,b)]=(hits,total)
    return res
for n in range(2,7):
    print(n,check(n,(min(2,n-1),n)),flush=True)
