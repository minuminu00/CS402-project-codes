from pysms.graph_builder import GraphEncodingBuilder
from itertools import combinations
from pysms.counters import counterFunction
import sys

n = 6
m = 6

def pos(i):
    return i

def neg(i):
    return 2*n-i-1

def cpos(i):
    return 2*n+i

def F1(builder:GraphEncodingBuilder, n, m):
    for i, j in combinations(list(range(m)), 2) :
        clause = [-builder.var_edge(cpos(i),cpos(j))]
        builder.append(clause)


def F2(builder:GraphEncodingBuilder, n, m):
    for i in range(0, n):
        clause = []
        clause2 = []
        for j in range(0, m):
            clause.append(builder.var_edge(pos(i), cpos(j)))
            clause2.append(builder.var_edge(neg(i), cpos(j)))
        builder.append(clause)
        builder.append(clause2)

    # F3: for all i∈[n], j∈[m]: ¬e_{i,j} ∨ ¬e_{−i,j}
def F3(builder:GraphEncodingBuilder, n, m):
    for i in range(n):
        for j in range(m):
            clause = [
                -builder.var_edge(pos(i),    cpos(j)),
                -builder.var_edge(neg(i),    cpos(j)),
            ]
            builder.append(clause)


def setClauseDegreeK(builder:GraphEncodingBuilder, n, m, k): # F5
    for j in range(m):
        counterFunction([builder.var_edge(i, cpos(j)) for i in range(2*n)], k, builder, builder, k, k)

def setMaxVarAppearanceS(builder:GraphEncodingBuilder, n, m, s): #F4v
    for i in range(n):
        vertices = []
        vertices.extend([builder.var_edge(pos(i), cpos(j)) for j in range(m)])
        vertices.extend([builder.var_edge(neg(i), cpos(j)) for j in range(m)])
        counterFunction(vertices, s, builder, builder, s, 0)

def F6(builder: GraphEncodingBuilder, n: int, m: int):
    # literal i ∈ {±1,…,±n} 을 0..2n-1 로, clause j ∈ [0..m-1] 을 2n..2n+m-1 로 매핑
    def litPos(lit: int) -> int:
        return pos(lit-1) if lit>0 else neg(-lit-1)

    # 모든 i, j 에 대해 φ_{i,j} 를 CNF 로 추가
    for i in range(1, n+1):
        for sign in (+1, -1):
            lit = sign * i
            for j in range(m):
                # 1) ψ_{i,j,j'} 생성: 각 j'≠j 에 대해 AND of ORs
                psi_map: dict[int,int] = {}
                for j_p in range(m):
                    if j_p == j:
                        continue
                    # 각 i'≠±i 에 대해 clause (¬e_{i',j'} ∨ ¬e_{−i',j'}) 를 OR gate 로 만듦
                    disjs = []
                    for i2 in range(1, n+1):
                        for sign2 in (+1, -1):
                            lit2 = sign2 * i2
                            if lit2 == lit or lit2 == -lit:
                                continue
                            e1 = builder.var_edge(litPos(lit2),  cpos(j))
                            e2 = builder.var_edge(litPos(-lit2), cpos(j_p))
                            # OR(¬e1, ¬e2)
                            disjs.append(builder.CNF_OR([-e1, -e2]))
                    # ψ_{i,j,j'} := AND(disjs)
                    psi_map[j_p] = builder.CNF_AND(disjs)

                # 2) φ_{i,j} 생성: ¬e_{i,j} ∨ ⋁_{j'≠j}( e_{−i,j'} ∧ ψ_{i,j,j'} )
                e_ij = builder.var_edge(litPos(lit), cpos(j))
                conjs = []
                for j_p, psi_var in psi_map.items():
                    e_neg = builder.var_edge(litPos(-lit), cpos(j_p))
                    # t_{j'} := AND(e_{−i,j'}, ψ)
                    conjs.append(builder.CNF_AND([e_neg, psi_var]))
                # φ := OR(¬e_{i,j}, *conjs)
                phi = builder.CNF_OR([-e_ij] + conjs)

                # 3) F6 에서는 φ_{i,j} 가 모두 true 여야 하므로 unit clause 로 추가
                builder.append([phi])


def F7(builder:GraphEncodingBuilder, n, m):
    for i in range(n):
        #builder.append([builder.var_edge(pos(i), neg(i))])
        for i_p in range(n):
            if(i != i_p): 
                builder.append([-builder.var_edge(pos(i), neg(i_p))])
    
    for i, i_p in combinations(list(range(n)), 2):
        builder.append([-builder.var_edge(pos(i), pos(i_p))])
        builder.append([-builder.var_edge(neg(i), neg(i_p))])
        pass


def setUNSATChecker(builder:GraphEncodingBuilder, n, m):
    alpha = [builder.id() for i in range(n)]

    z_vars = []

    for j in range(m):
        z = builder.id()
        z_vars.append(z)

        for i in range(n):
            builder.append([-z, -alpha[i], -builder.var_edge(pos(i), cpos(j))])
            builder.append([-z, alpha[i], -builder.var_edge(neg(i), cpos(j))])

    builder.append(z_vars)

def main():
    
    k = 3
    s = 3
    # directed=False → 무향 그래프
    builder = GraphEncodingBuilder(2*n + m, directed=False)

    F1(builder, n, m)
    F2(builder, n, m)
    F3(builder, n, m)
    setClauseDegreeK(builder, n, m, k)
    setMaxVarAppearanceS(builder, n, m, s)
    F6(builder,n,m)
    F7(builder, n, m)

    #builder.print_dimacs(sys.stdout)
    builder.solve(allGraphs=True)

if __name__ == "__main__":
    main()
    